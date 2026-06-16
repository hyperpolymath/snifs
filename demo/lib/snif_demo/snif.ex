# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
defmodule Snif do
  @moduledoc """
  The SNIF behaviour: the stable, host-facing contract for invoking a
  crash-isolated WASM guest as a "Safer NIF".

  This is the public surface that replaces `SnifDemo.Loader.call/3`
  (ADR-003 per-call instantiation) with a pooled, long-lived instance
  model that PRESERVES per-call isolation while amortizing the expensive
  compile step.

  ## Contract (what every implementation MUST guarantee)

    1. ISOLATION (unchanged from the per-call model):
       A guest trap surfaces as `{:error, reason}` and NEVER kills the
       calling BEAM process nor the pool. This is the existing SNIF
       crash-isolation guarantee (tested by 11 ExUnit cases).

    2. NO-SHARED-STATE between calls:
       Two calls — even back-to-back on the same physical OS thread / pool
       worker — observe ZERO guest state carried over. Mutable guest
       globals (e.g. `safe_nif.zig`'s `runtime_index`/`crash_layout`) and
       linear memory are restored to their post-instantiation values before
       the next call begins. The realised mechanism in wasmex 0.14 is
       RE-INSTANTIATION (`Wasmex.Instance.new/4`), which re-runs the
       module's data-segment init and global initializers — see
       ADR-004. There is no in-place memory/global reset primitive in
       wasmex 0.14, and in-place reuse is therefore forbidden because the
       guest has mutable globals.

    3. LIVENESS / DoS guard (new — safety -> safety+liveness):
       A runaway guest (infinite loop, fuel exhaustion) is forcibly
       trapped, not allowed to hang the pool. In wasmex 0.14 this is fuel
       (`EngineConfig.consume_fuel/2` + `StoreOrCaller.set_fuel/2`) backed
       by the `call_function/4` host-side timeout. (Epoch interruption is
       NOT in wasmex 0.14; fuel is the deterministic guard we have — see
       ADR-004 §Liveness.)

  ## The behaviour

  An implementation module declares the guest it wraps and the exported
  functions it permits. The pool calls `wasm_bytes/0` ONCE at warm-up
  (compile-once) and `exports/0` to validate / whitelist call targets.
  """

  @typedoc "Result of a guest call: success values list, or an isolated error."
  @type result :: {:ok, [number()]} | {:error, term()}

  @typedoc """
  Why a call failed. Distinguishes the three real outcome origins the
  Agda `SnifVerdict` model flagged as conflated (load error vs guest trap):

    * `{:trap, reason}`       guest ran and faulted (panic / oob / fuel-out)
    * `{:fuel_exhausted, _}`  liveness guard fired (runaway guest)
    * `{:timeout, _}`         host backstop fired (call exceeded wall clock)
    * `{:load, reason}`       module/instance could not be created (no guest ran)
    * `{:no_such_export, n}`  call target not in the whitelist
    * `{:pool, reason}`       pool was unavailable (e.g. checkout timeout)
  """
  @type error_reason ::
          {:trap, binary()}
          | {:fuel_exhausted, term()}
          | {:timeout, term()}
          | {:load, binary()}
          | {:no_such_export, String.t()}
          | {:pool, term()}

  @doc "Raw bytes of the (ReleaseSafe!) guest `.wasm`. Read once at warm-up."
  @callback wasm_bytes() :: {:ok, binary()} | {:error, term()}

  @doc """
  Whitelist of callable exports as `{name, arity}`. The pool refuses any
  call whose name is not in this list (defence in depth above wasmex's own
  `function_exists`).
  """
  @callback exports() :: [{String.t(), non_neg_integer()}]

  @doc """
  Fuel budget granted to each fresh instance (the per-call liveness bound).
  Return `:unlimited` only for trusted guests; the SNIF default is bounded.
  """
  @callback fuel_per_call() :: pos_integer() | :unlimited

  @doc "Optional store memory cap in bytes (maps to `%Wasmex.StoreLimits{memory_size:}`)."
  @callback memory_limit_bytes() :: pos_integer() | :unlimited

  @optional_callbacks memory_limit_bytes: 0

  # ── Convenience client API (delegates to the pool for a guest module) ──

  @doc """
  Call `function_name` on a pooled instance of `guest_mod`, with full
  SNIF isolation + no-shared-state + liveness guard.

  `guest_mod` is a module implementing this behaviour and registered as a
  pool (see `Snif.Pool`). Returns `t:result/0`.
  """
  @spec call(module(), String.t(), [number()], keyword()) :: result()
  def call(guest_mod, function_name, args \\ [], opts \\ []) do
    Snif.Pool.call(guest_mod, function_name, args, opts)
  end
end
