# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
defmodule SnifDemo.SafeNif do
  @moduledoc """
  A concrete `Snif` guest: the `safe_nif_ReleaseSafe.wasm` module
  (built from `zig/src/safe_nif.zig` with `-OReleaseSafe`).

  This is the worked example of the SNIF behaviour and the consumer the pool
  is wired to in `SnifDemo.Application`. It replaces the ADR-003 per-call
  `SnifDemo.Loader.call(@safe, fun, args)` usage with the pooled, long-lived
  instance model:

      iex> SnifDemo.SafeNif.fibonacci(10)
      {:ok, [55]}
      iex> SnifDemo.SafeNif.crash_oob()
      {:error, {:trap, _reason}}        # BEAM survives; instance is dead, pool lives
      iex> SnifDemo.SafeNif.still_alive()
      {:ok, [42]}                       # next call gets a FRESH, clean instance

  ## ReleaseSafe invariant

  We deliberately point at the **ReleaseSafe** artifact: under ReleaseFast the
  crash demos turn UB into silent wrong answers instead of traps, defeating the
  isolation thesis. `wasm_bytes/0` fails fast (a load-class `{:error, _}` at
  warm-up) if the artifact is missing, mirroring a NIF that won't load.
  """

  @behaviour Snif

  # Path resolved at runtime, not compile time, so the artifact can be rebuilt
  # by `just build-wasm` without recompiling Elixir.
  @wasm_relpath ["..", "..", "priv", "safe_nif_ReleaseSafe.wasm"]

  # Per-call fuel budget. fibonacci(10) costs well under 10_000 fuel units;
  # a runaway/looping guest exhausts this and traps deterministically as
  # `{:error, {:fuel_exhausted, _}}` (verified against wasmtime 44:
  # "wasm trap: all fuel consumed by WebAssembly"). Tune per workload.
  @fuel_per_call 5_000_000

  # 16 MiB linear-memory cap (the .wasm declares 17 pages ≈ 1.1 MiB initial;
  # this bounds growth and is well above what the scalar demos need).
  @memory_limit 16 * 1024 * 1024

  @impl Snif
  def wasm_bytes do
    path = Path.join([__DIR__ | @wasm_relpath]) |> Path.expand()

    case File.read(path) do
      {:ok, bytes} -> {:ok, bytes}
      {:error, reason} -> {:error, {:wasm_artifact_missing, path, reason}}
    end
  end

  @impl Snif
  def exports do
    [
      {"fibonacci", 1},
      {"checked_add", 2},
      {"crash_oob", 0},
      {"crash_unreachable", 0},
      {"crash_panic", 0},
      {"crash_overflow", 0},
      {"crash_div_zero", 0},
      {"still_alive", 0}
    ]
  end

  @impl Snif
  def fuel_per_call, do: @fuel_per_call

  @impl Snif
  def memory_limit_bytes, do: @memory_limit

  # ── Convenience wrappers (typed call surface over the generic Snif.call) ──

  @spec fibonacci(integer()) :: Snif.result()
  def fibonacci(n) when is_integer(n), do: Snif.call(__MODULE__, "fibonacci", [n])

  @spec checked_add(integer(), integer()) :: Snif.result()
  def checked_add(a, b) when is_integer(a) and is_integer(b),
    do: Snif.call(__MODULE__, "checked_add", [a, b])

  @spec still_alive() :: Snif.result()
  def still_alive, do: Snif.call(__MODULE__, "still_alive", [])

  @spec crash_oob() :: Snif.result()
  def crash_oob, do: Snif.call(__MODULE__, "crash_oob", [])

  @spec crash_unreachable() :: Snif.result()
  def crash_unreachable, do: Snif.call(__MODULE__, "crash_unreachable", [])

  @spec crash_panic() :: Snif.result()
  def crash_panic, do: Snif.call(__MODULE__, "crash_panic", [])

  @spec crash_overflow() :: Snif.result()
  def crash_overflow, do: Snif.call(__MODULE__, "crash_overflow", [])

  @spec crash_div_zero() :: Snif.result()
  def crash_div_zero, do: Snif.call(__MODULE__, "crash_div_zero", [])
end
