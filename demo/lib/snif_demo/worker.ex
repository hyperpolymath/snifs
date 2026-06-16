# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
defmodule Snif.Worker do
  @moduledoc """
  A long-lived pool worker that owns ONE compiled `Wasmex.Module` and a
  recyclable `Wasmex.Store`, and serves calls with per-call
  re-instantiation.

  ## The lifecycle this implements (the heart of ADR-004)

      warm-up (once):
        bytes = guest.wasm_bytes()            # read .wasm ONCE
        engine = Engine.new(consume_fuel: true)
        store  = Store.new(limits, engine)    # fuel-capable, memory-capped
        module = Module.compile(store, bytes) # COMPILE ONCE (the expensive bit)

      per call:
        store  = ensure_fresh_store(state)    # recycle if instantiations >= max
        inst   = Instance.new(store, module)  # RE-INSTANTIATE  -> clean state
        set_fuel(store, fuel_per_call)        # liveness budget for THIS call
        result = call(store, inst, name, args, call_timeout)
        reply result; checkin

  ### Why re-instantiate every call (NO-SHARED-STATE)

  wasmex 0.14 has NO in-place memory/global reset primitive (verified:
  no `reset`/`reinstantiate`/`fresh` function exists in the API). The guest
  (`safe_nif.zig`) has MUTABLE module-level globals
  (`runtime_index`, `runtime_zero`, `runtime_max`, `crash_layout`) that live
  in WASM globals / linear-memory data segments. If we reused one instance
  across calls, a call that mutated a global would be observable by the next
  call — breaking the per-call NIF isolation contract.

  A fresh `Instance.new/4` re-runs the module's data-segment initialization
  and re-evaluates every global's initializer expression, so each call sees
  EXACTLY the post-instantiation state — identical to what the ADR-003
  per-call model gave, but WITHOUT re-reading bytes and WITHOUT recompiling.
  Re-instantiation is the cheap half of the old per-call cost; compile is the
  expensive half and is now paid once.

  ### Why recycle the Store (bounded leak)

  `Wasmex.Store`'s own moduledoc: a Store "never release[s] this memory" for
  instances created within it and is "unsuitable for creating an unbounded
  number of instances". So instances accumulate in the Store. We therefore
  drop and rebuild the Store (and recompile the Module into it) every
  `max_instantiations` calls. The Module must be recompiled because a Module
  is bound to the Store it was compiled in. This bounds resident memory at
  roughly `max_instantiations` live-instance footprints per worker.

  ### Liveness guard (fuel + host timeout; NO epoch in 0.14)

  The engine is built with `consume_fuel: true`; each fresh Store is given
  `fuel_per_call` units via `StoreOrCaller.set_fuel/2`. A runaway guest
  exhausts fuel and TRAPS deterministically -> `{:error, {:fuel_exhausted,_}}`.
  Above that, `Wasmex.call_function/4`'s timeout is a wall-clock backstop for
  anything fuel cannot bound (e.g. a host import that blocks). Epoch-based
  interruption is NOT available in wasmex 0.14, so fuel is the deterministic
  primitive; when the project moves to a wasmex version exposing epochs, an
  epoch deadline can be added alongside fuel without changing this contract.
  """

  use GenServer
  require Logger

  alias Wasmex.{Engine, EngineConfig, Instance, Module, Store, StoreLimits, StoreOrCaller}

  defmodule State do
    @moduledoc false
    defstruct guest_mod: nil,
              bytes: nil,
              engine: nil,
              store: nil,
              module: nil,
              fuel: nil,
              limits: nil,
              max_instantiations: 256,
              instantiations: 0
  end

  # ── API used by the pool ───────────────────────────────────────────────

  @spec start_link(module(), pos_integer()) :: {:ok, pid()} | {:error, term()}
  def start_link(guest_mod, max_instantiations) do
    GenServer.start_link(__MODULE__, {guest_mod, max_instantiations})
  end

  @doc """
  Run one unit of work. The worker replies to `from` directly with
  `{:ok, result}` (where `result` is a `t:Snif.result/0`), then messages
  `pool` with `{:checkin, self()}`. Cast-style so the pool manager never
  blocks on a slow guest.
  """
  @spec run(pid(), GenServer.from(), String.t(), [number()], pos_integer(), pid()) :: :ok
  def run(worker, from, function_name, args, call_timeout, pool) do
    GenServer.cast(worker, {:run, from, function_name, args, call_timeout, pool})
  end

  @doc """
  Run a STATEFUL transaction against ONE fresh instance. The worker
  re-instantiates once (no-shared-state at the TRANSACTION boundary), grants
  fuel, then invokes `fun.(instance, store)` — letting the caller make several
  exported-function calls that share one linear memory (the Buffer ABI:
  `snif_alloc` -> `write` -> op -> `snif_dealloc`). The transaction's whole fuel
  budget is the per-call budget (one instantiation = one budget), so a runaway
  multi-step transaction still traps.

  The caller's `fun` is run inside a `try`, so a guest trap or a host-side
  marshalling error becomes `{:error, _}` and the worker never crashes. Replies
  `{:ok, result}` to `from`, then checks in. Used by `Snif.Pool.with_instance/3`.
  """
  @spec run_with(pid(), GenServer.from(), (term(), term() -> Snif.result()), pid()) :: :ok
  def run_with(worker, from, fun, pool) do
    GenServer.cast(worker, {:run_with, from, fun, pool})
  end

  # ── Warm-up: read once, compile once ───────────────────────────────────

  @impl true
  def init({guest_mod, max_instantiations}) do
    with {:ok, bytes} <- guest_mod.wasm_bytes(),
         {:ok, engine} <- Engine.new(%EngineConfig{consume_fuel: true}),
         limits = build_limits(guest_mod),
         {:ok, store} <- Store.new(limits, engine),
         {:ok, module} <- Module.compile(store, bytes) do
      state = %State{
        guest_mod: guest_mod,
        bytes: bytes,
        engine: engine,
        store: store,
        module: module,
        fuel: guest_mod.fuel_per_call(),
        limits: limits,
        max_instantiations: max_instantiations,
        instantiations: 0
      }

      {:ok, state}
    else
      {:error, reason} -> {:stop, {:warmup_failed, reason}}
    end
  end

  defp build_limits(guest_mod) do
    mem =
      if function_exported?(guest_mod, :memory_limit_bytes, 0) do
        case guest_mod.memory_limit_bytes() do
          :unlimited -> nil
          n when is_integer(n) -> n
        end
      else
        nil
      end

    %StoreLimits{memory_size: mem}
  end

  # ── Per-call: re-instantiate -> fuel -> call -> reply -> checkin ────────

  @impl true
  def handle_cast({:run, from, function_name, args, call_timeout, pool}, state) do
    result = do_call(state, function_name, args, call_timeout)
    GenServer.reply(from, {:ok, result})

    # Advance lifecycle: count this instantiation; recycle Store if due.
    state = %{state | instantiations: state.instantiations + 1}
    state = maybe_recycle_store(state)

    send(pool, {:checkin, self()})
    {:noreply, state}
  end

  # Stateful transaction: one fresh instance, one fuel budget, caller-supplied
  # multi-step body. Counts as a single instantiation for recycling purposes.
  @impl true
  def handle_cast({:run_with, from, fun, pool}, state) do
    result = do_transaction(state, fun)
    GenServer.reply(from, {:ok, result})

    state = %{state | instantiations: state.instantiations + 1}
    state = maybe_recycle_store(state)

    send(pool, {:checkin, self()})
    {:noreply, state}
  end

  # Whitelist check -> fresh instance (the no-shared-state reset) ->
  # fuel grant -> guarded call -> normalised result. Every failure path
  # returns {:error, _}; the worker process never crashes on a guest fault.
  defp do_call(state, function_name, args, call_timeout) do
    guest_mod = state.guest_mod

    cond do
      not whitelisted?(guest_mod, function_name) ->
        {:error, {:no_such_export, function_name}}

      true ->
        with {:ok, inst} <- Instance.new(state.store, state.module, %{}, []),
             :ok <- grant_fuel(state) do
          start = System.monotonic_time(:microsecond)

          case call_exported(state.store, inst, function_name, args, call_timeout) do
            {:ok, values} ->
              {:ok, values}

            {:error, reason} ->
              classify_failure(reason, state, start, call_timeout)
          end
        else
          # Instance.new or fuel setup failed: load-class error, no guest ran.
          # Capture the real failure reason rather than a placeholder atom.
          {:error, reason} ->
            {:error, {:load, inspect_reason(reason)}}
        end
    end
  end

  # Stateful transaction body: ONE fresh instance + ONE fuel budget, then run
  # the caller's multi-step `fun.(instance, store)` inside a try so any guest
  # trap / host marshalling error is isolated to {:error, _}. The instance and
  # store are scoped to this transaction and discarded afterwards (the next
  # transaction gets a fresh instance => no shared state across transactions).
  defp do_transaction(state, fun) do
    with {:ok, inst} <- Instance.new(state.store, state.module, %{}, []),
         :ok <- grant_fuel(state) do
      try do
        case fun.(inst, state.store) do
          {:ok, _} = ok -> ok
          {:error, _} = err -> err
          other -> {:error, {:trap, inspect_reason(other)}}
        end
      rescue
        e -> {:error, {:trap, inspect_reason(e)}}
      catch
        kind, reason -> {:error, {:trap, inspect_reason({kind, reason})}}
      end
    else
      {:error, reason} -> {:error, {:load, inspect_reason(reason)}}
    end
  end

  defp whitelisted?(guest_mod, name) do
    Enum.any?(guest_mod.exports(), fn {n, _arity} -> n == name end)
  end

  # Grant THIS call's fuel into the (current) store. No-op if :unlimited.
  defp grant_fuel(%State{fuel: :unlimited}), do: :ok

  defp grant_fuel(%State{store: store, fuel: fuel}) when is_integer(fuel) do
    StoreOrCaller.set_fuel(store, fuel)
  end

  # Drive the instance from THIS process so the long-lived store/module never
  # leave the worker. The wasmex NIF computes the call on a Tokio task and
  # delivers the result by replying to the GenServer `from` we pass in.
  #
  # GROUND-TRUTH (pinned against vendored wasmex 0.14.0 Rust NIF,
  # native/wasmex/src/instance.rs:215-258): `instance_call_exported_function`
  # spawns a Tokio task and, on completion, runs
  #
  #     let (caller_pid, ref_term) = from.decode::<(LocalPid, Term)>();
  #     env.send(&caller_pid, make_tuple(env, &[ref_term, result_term]));
  #
  # i.e. it sends EXACTLY `{ref, result}` to the pid in the `from` tuple —
  # the standard `GenServer.reply/2` wire format. So with `from = {self(), ref}`
  # the message that lands here is `{ref, result}` and nothing else. `result`
  # is `{:ok, [values]}` on success or `{:error, binary()}` on trap/fuel/not-found
  # (instance.rs:296-320 wraps every wasmtime trap as an `error_tuple` binary).
  # There is no `{:returned_function_call, ...}` shape in 0.14; do not add one.
  #
  # The `after call_timeout` clause is a wall-clock backstop ABOVE fuel: it
  # catches the (rare) case fuel cannot bound — e.g. a blocking host import —
  # and the case where the NIF task somehow never replies. On timeout we return
  # `{:error, {:timeout, _}}` WITHOUT killing the worker; the orphaned Tokio
  # task, if it later completes, sends a stale `{ref, _}` that the next
  # `receive` would ignore because each call uses a fresh `ref`.
  defp call_exported(store, inst, name, args, call_timeout) do
    ref = make_ref()
    from = {self(), ref}

    case Wasmex.Instance.call_exported_function(store, inst, name, args, from) do
      :ok ->
        receive do
          {^ref, result} -> normalise(result)
        after
          call_timeout -> {:error, {:timeout, call_timeout}}
        end

      {:error, reason} ->
        # Synchronous failure to even dispatch the call (load-class).
        {:error, {:load, inspect_reason(reason)}}

      other ->
        {:error, {:trap, inspect_reason(other)}}
    end
  end

  defp normalise({:ok, values}) when is_list(values), do: {:ok, values}
  defp normalise({:error, reason}), do: {:error, {:trap, inspect_reason(reason)}}
  defp normalise(other), do: {:error, {:trap, inspect_reason(other)}}

  # Fuel exhaustion surfaces from wasmtime as a trap; we tag it distinctly
  # when the reason text indicates fuel, else keep it a generic trap.
  defp classify_failure(reason, _state, _start, _call_timeout) do
    text = inspect_reason(reason)

    cond do
      String.contains?(text, ["fuel", "all fuel consumed"]) ->
        {:error, {:fuel_exhausted, text}}

      true ->
        {:error, {:trap, text}}
    end
  end

  defp inspect_reason(r) when is_binary(r), do: r
  defp inspect_reason(r), do: inspect(r)

  # ── Store recycling (bounded-leak management) ──────────────────────────

  defp maybe_recycle_store(%State{instantiations: n, max_instantiations: max} = state)
       when n >= max do
    Logger.debug("SNIF worker recycling Store after #{n} instantiations")

    with {:ok, engine} <- Engine.new(%EngineConfig{consume_fuel: true}),
         {:ok, store} <- Store.new(state.limits, engine),
         {:ok, module} <- Module.compile(store, state.bytes) do
      # Old store/module become unreferenced and are reclaimed by BEAM GC,
      # releasing all accumulated instances at once.
      %{state | engine: engine, store: store, module: module, instantiations: 0}
    else
      {:error, reason} ->
        Logger.error("SNIF Store recycle failed: #{inspect(reason)}; keeping old store")
        # Keep serving on the old (leaky) store rather than dying.
        state
    end
  end

  defp maybe_recycle_store(state), do: state
end
