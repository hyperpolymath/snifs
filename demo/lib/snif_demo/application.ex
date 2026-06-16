# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
defmodule SnifDemo.Application do
  @moduledoc """
  Wires the SNIF instance pool into the application supervision tree.

  This is the "wire-first" step: `Snif.Pool` / `Snif.Worker` / `SnifDemo.SafeNif`
  are not a finished unit until a pool is actually STARTED by a supervisor and
  reachable via `Snif.call/4`. The tree is:

      SnifDemo.Supervisor (one_for_one)
      └── {Snif.Pool, guest_mod: SnifDemo.SafeNif, ...}   (pool manager)
          ├── Snif.Worker (compile-once module + recyclable store) × pool_size
          └── ...

  A worker crash is converted to `{:error, _}` and never propagates here; a
  worker that does die (rare) is replaced by the pool itself (`handle_info
  {:EXIT,...}`), so this supervisor only restarts the *pool manager* if the
  whole pool dies.

  ## Pooling is opt-in for tests

  We only auto-start the pool when the ReleaseSafe artifact is present, so the
  app boots even before `just build-wasm` has run (the legacy `SnifDemo.Loader`
  per-call path needs no pool). The pool-exercising ExUnit tests start their
  own pool explicitly and are tagged `:pool`.
  """

  use Application

  @impl true
  def start(_type, _args) do
    children = pool_children()

    opts = [strategy: :one_for_one, name: SnifDemo.Supervisor]
    Supervisor.start_link(children, opts)
  end

  # Start the SafeNif pool only if its .wasm exists; otherwise boot without it
  # (Loader-based tests and the FFT demo do not need the pool).
  defp pool_children do
    case SnifDemo.SafeNif.wasm_bytes() do
      {:ok, _bytes} ->
        [
          {Snif.Pool,
           guest_mod: SnifDemo.SafeNif,
           pool_size: pool_size(),
           max_instantiations: 256}
        ]

      {:error, _missing} ->
        []
    end
  end

  defp pool_size do
    # One worker per scheduler online, capped, is a sane default for a
    # CPU-bound (no-WASI/no-IO, ADR-002) guest.
    System.schedulers_online() |> min(8) |> max(1)
  end
end
