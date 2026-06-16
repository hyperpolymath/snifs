# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
defmodule Snif.Pool do
  @moduledoc """
  A pool of long-lived `Snif.Worker` GenServers, each holding a
  COMPILED-ONCE `Wasmex.Module` and a recyclable `Wasmex.Store`.

  This replaces ADR-003 (a fresh `Wasmex.start_link/1` — read bytes +
  compile + instantiate — PER CALL) with:

    * compile-once at warm-up (the expensive step is paid once per worker);
    * re-instantiate-per-call (the cheap step gives a guaranteed-clean
      guest, preserving NO-SHARED-STATE — see ADR-004);
    * fuel per fresh instance (the liveness / DoS guard);
    * Store recycling after `:max_instantiations` (because a wasmex 0.14
      Store NEVER frees old instances — its own moduledoc warns it is
      "unsuitable for creating an unbounded number of instances").

  ## Why a custom pool and not NimblePool / poolboy

  We need a per-checkout RE-INSTANTIATION step and Store-recycling logic
  that those libraries do not model. The worker owns its `%Module{}` and
  performs the reset itself, so the pool only has to do checkout/checkin
  and back-pressure. Keeping it dependency-free also keeps the demo
  buildable on the constrained env (OTP 25 here; OTP 28 target).

  ## Supervision tree

      Snif.Pool.Supervisor (one_for_one)
      └── for each registered guest module G:
          Snif.Pool.WorkerSup[G]   (DynamicSupervisor / simple pool)
          ├── Snif.Worker  (compiled module + store, instance #k)
          ├── Snif.Worker
          └── ... (pool_size workers)

  Start a pool for a guest with `start_pool/2`, then call via
  `Snif.call/4` (or `Snif.Pool.call/4`).
  """

  use GenServer
  require Logger

  @default_pool_size 4
  # Recycle a worker's Store after this many instantiations, to bound the
  # documented wasmex-Store instance leak. Conservatively well under the
  # 10_000 StoreLimits default.
  @default_max_instantiations 256
  @default_checkout_timeout 5_000

  defmodule State do
    @moduledoc false
    defstruct guest_mod: nil,
              workers: [],
              # queue of available worker pids
              free: :queue.new(),
              # FIFO of waiting {from, function, args, opts, deadline}
              waiting: :queue.new(),
              busy: MapSet.new()
  end

  # ── Public API ─────────────────────────────────────────────────────────

  @doc """
  Start a pool for `guest_mod` (a module implementing the `Snif` behaviour).

  Options:
    * `:pool_size`           - number of workers (default #{@default_pool_size})
    * `:max_instantiations`  - Store recycle threshold (default #{@default_max_instantiations})
    * `:name`                - registered pool name (default `via` guest_mod)
  """
  @spec start_pool(module(), keyword()) :: {:ok, pid()} | {:error, term()}
  def start_pool(guest_mod, opts \\ []) do
    name = Keyword.get(opts, :name, pool_name(guest_mod))
    GenServer.start_link(__MODULE__, {guest_mod, opts}, name: name)
  end

  @doc """
  Child spec so a pool can be placed directly in a supervision tree
  (the wiring used by `SnifDemo.Application`):

      children = [
        {Snif.Pool, guest_mod: SnifDemo.SafeNif, pool_size: 4}
      ]

  The `:id` is keyed on the guest module so multiple guest pools coexist
  under one supervisor. A warm-up failure (e.g. missing/bad `.wasm`) makes
  `init/1` `{:stop, ...}`, which the supervisor surfaces as a start error —
  fail-fast, exactly like a NIF that won't load.
  """
  @spec child_spec(keyword()) :: Supervisor.child_spec()
  def child_spec(opts) do
    {guest_mod, start_opts} = Keyword.pop!(opts, :guest_mod)

    %{
      id: pool_name(guest_mod),
      start: {__MODULE__, :start_pool, [guest_mod, start_opts]},
      type: :worker,
      restart: :permanent
    }
  end

  @doc """
  Run `function_name(args)` on a pooled instance of `guest_mod`.

  Performs: checkout -> worker re-instantiates a fresh guest -> set fuel ->
  call (with host timeout) -> checkin (and Store-recycle if due).

  Returns `t:Snif.result/0`. A guest trap, fuel exhaustion, or timeout all
  come back as `{:error, _}` WITHOUT killing the caller or the pool.
  """
  @spec call(module(), String.t(), [number()], keyword()) :: Snif.result()
  def call(guest_mod, function_name, args \\ [], opts \\ []) do
    checkout_timeout = Keyword.get(opts, :checkout_timeout, @default_checkout_timeout)
    # `call_function/4` host timeout; the liveness backstop above fuel.
    call_timeout = Keyword.get(opts, :call_timeout, 5_000)

    case GenServer.call(
           pool_name(guest_mod),
           {:checkout, function_name, args, call_timeout},
           # outer timeout must exceed inner so we get a clean {:error,_}
           checkout_timeout + call_timeout + 1_000
         ) do
      {:ok, result} -> result
      {:error, _} = err -> err
    end
  catch
    :exit, {:timeout, _} -> {:error, {:pool, :checkout_timeout}}
    :exit, {:noproc, _} -> {:error, {:pool, :not_started}}
  end

  @doc """
  Run a STATEFUL transaction on one pooled, freshly-instantiated guest:
  check out a worker, re-instantiate (no-shared-state at the transaction
  boundary), grant fuel, then run `fun.(instance, store)` — which may make
  several `Wasmex.Instance.call_exported_function/5` calls that share ONE
  linear memory. This is the lifecycle primitive the Buffer ABI needs
  (`snif_alloc` -> write bytes -> op -> `snif_dealloc`), since a per-call
  re-instantiation would invalidate the pointer between steps.

  `fun` MUST return `t:Snif.result/0`. Any trap or marshalling error inside it
  is isolated to `{:error, _}` by the worker; the worker and pool survive.
  """
  @spec with_instance(module(), keyword(), (term(), term() -> Snif.result())) :: Snif.result()
  def with_instance(guest_mod, opts \\ [], fun) when is_function(fun, 2) do
    checkout_timeout = Keyword.get(opts, :checkout_timeout, @default_checkout_timeout)
    call_timeout = Keyword.get(opts, :call_timeout, 5_000)

    case GenServer.call(
           pool_name(guest_mod),
           {:checkout_with, fun},
           checkout_timeout + call_timeout + 1_000
         ) do
      {:ok, result} -> result
      {:error, _} = err -> err
    end
  catch
    :exit, {:timeout, _} -> {:error, {:pool, :checkout_timeout}}
    :exit, {:noproc, _} -> {:error, {:pool, :not_started}}
  end

  defp pool_name(guest_mod), do: Module.concat(__MODULE__, guest_mod)

  # ── GenServer (the pool manager) ───────────────────────────────────────

  @impl true
  def init({guest_mod, opts}) do
    Process.flag(:trap_exit, true)
    pool_size = Keyword.get(opts, :pool_size, @default_pool_size)
    max_inst = Keyword.get(opts, :max_instantiations, @default_max_instantiations)

    # Warm up: each worker compiles the module ONCE here. Compile failure
    # at warm-up is a hard start error (fail fast, like a NIF that won't load).
    case start_workers(guest_mod, pool_size, max_inst) do
      {:ok, workers} ->
        free = Enum.reduce(workers, :queue.new(), &:queue.in(&1, &2))
        {:ok, %State{guest_mod: guest_mod, workers: workers, free: free}}

      # `reason` is already a worker `{:warmup_failed, _}`; pass it through
      # unwrapped so we don't get `{:warmup_failed, {:warmup_failed, _}}`.
      {:error, reason} ->
        {:stop, reason}
    end
  end

  defp start_workers(guest_mod, n, max_inst) do
    Enum.reduce_while(1..n, {:ok, []}, fn _i, {:ok, acc} ->
      case Snif.Worker.start_link(guest_mod, max_inst) do
        {:ok, pid} ->
          {:cont, {:ok, [pid | acc]}}

        # Worker init failed (e.g. `{:warmup_failed, {:wasm_artifact_missing,_}}`).
        # Tear down any workers already started so we don't leak them on a
        # partial warm-up, then report the reason.
        {:error, r} ->
          Enum.each(acc, &Process.exit(&1, :shutdown))
          {:halt, {:error, r}}
      end
    end)
  end

  # Both checkout variants normalise to a {from, work} pair where `work` is
  # either {:call, name, args, timeout} or {:transaction, fun}, then go through
  # one assign/back-pressure path.
  @impl true
  def handle_call({:checkout, name, args, call_timeout}, from, state) do
    assign_or_queue(from, {:call, name, args, call_timeout}, state)
  end

  @impl true
  def handle_call({:checkout_with, fun}, from, state) do
    assign_or_queue(from, {:transaction, fun}, state)
  end

  @impl true
  def handle_info({:checkin, worker}, state) do
    state = %{state | busy: MapSet.delete(state.busy, worker)}

    case :queue.out(state.waiting) do
      {{:value, {from, work}}, waiting} ->
        dispatch(worker, from, work)
        {:noreply, %{state | waiting: waiting, busy: MapSet.put(state.busy, worker)}}

      {:empty, _} ->
        {:noreply, %{state | free: :queue.in(worker, state.free)}}
    end
  end

  # A worker died (should be rare — workers convert traps to {:error,_} and
  # do not crash on guest faults). Replace it to keep the pool at size.
  @impl true
  def handle_info({:EXIT, dead, reason}, state) do
    if dead in state.workers do
      Logger.warning("SNIF worker #{inspect(dead)} died: #{inspect(reason)}; replacing")

      case Snif.Worker.start_link(state.guest_mod, @default_max_instantiations) do
        {:ok, new_pid} ->
          workers = [new_pid | List.delete(state.workers, dead)]

          {:noreply,
           %{
             state
             | workers: workers,
               free: :queue.in(new_pid, requeue_without(state.free, dead)),
               busy: MapSet.delete(state.busy, dead)
           }}

        {:error, _} ->
          {:noreply, %{state | workers: List.delete(state.workers, dead)}}
      end
    else
      {:noreply, state}
    end
  end

  def handle_info(_other, state), do: {:noreply, state}

  # ── Internal dispatch helpers ──────────────────────────────────────────

  # Assign a free worker, or queue the {from, work} for the next checkin.
  defp assign_or_queue(from, work, state) do
    case :queue.out(state.free) do
      {{:value, worker}, free} ->
        dispatch(worker, from, work)
        {:noreply, %{state | free: free, busy: MapSet.put(state.busy, worker)}}

      {:empty, _} ->
        {:noreply, %{state | waiting: :queue.in({from, work}, state.waiting)}}
    end
  end

  # Hand the unit of work to the worker; it replies to `from` directly and then
  # notifies us to check it back in.
  defp dispatch(worker, from, {:call, name, args, call_timeout}) do
    Snif.Worker.run(worker, from, name, args, call_timeout, self())
  end

  defp dispatch(worker, from, {:transaction, fun}) do
    Snif.Worker.run_with(worker, from, fun, self())
  end

  defp requeue_without(queue, pid) do
    queue |> :queue.to_list() |> Enum.reject(&(&1 == pid)) |> :queue.from_list()
  end
end
