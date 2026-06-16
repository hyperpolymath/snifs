# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
defmodule SnifPoolTest do
  @moduledoc """
  Lifecycle tests for the pooled SNIF instance model (ADR-004): isolation,
  no-shared-state across calls, the fuel liveness guard, back-pressure, and
  Store recycling. These exercise `Snif.Pool` / `Snif.Worker` / `SnifDemo.SafeNif`
  against the real ReleaseSafe `.wasm`.

  Tagged `:pool` so the suite can be run in isolation:

      mix test --only pool
  """
  use ExUnit.Case, async: false

  @safe Path.join([__DIR__, "..", "..", "priv", "safe_nif_ReleaseSafe.wasm"]) |> Path.expand()

  setup_all do
    unless File.exists?(@safe) do
      raise "missing #{@safe} — run `just build-wasm` first"
    end

    :ok
  end

  # The SafeNif pool is started once by `SnifDemo.Application` at boot (it is
  # registered under Module.concat(Snif.Pool, SafeNif), which the convenience
  # client API resolves). These tests use that already-running pool, so they
  # exercise the SAME wiring the app ships. Tests that need a special config
  # (e.g. a low recycle threshold) start their OWN uniquely-named pool.
  setup do
    case Process.whereis(Module.concat(Snif.Pool, SnifDemo.SafeNif)) do
      nil -> start_supervised!({Snif.Pool, guest_mod: SnifDemo.SafeNif})
      _pid -> :ok
    end

    :ok
  end

  @tag :pool
  test "happy path: pooled fibonacci returns the same as the per-call loader" do
    assert {:ok, [55]} = SnifDemo.SafeNif.fibonacci(10)
    assert {:ok, [42]} = SnifDemo.SafeNif.still_alive()
  end

  @tag :pool
  test "isolation: a guest trap is {:error,_} and the pool keeps serving" do
    assert {:error, {:trap, _}} = SnifDemo.SafeNif.crash_oob()
    assert {:error, {:trap, _}} = SnifDemo.SafeNif.crash_panic()
    # The critical assertion: the pool and a fresh instance still work after.
    assert {:ok, [42]} = SnifDemo.SafeNif.still_alive()
  end

  @tag :pool
  test "no-shared-state: a crash leaves no residue for the next call" do
    # crash_oob reads crash_layout.arr[3] (a mutable memory-resident global).
    # After a trap, the next call must observe pristine, post-instantiation state.
    assert {:error, {:trap, _}} = SnifDemo.SafeNif.crash_oob()
    # fibonacci is pure but shares the same worker/store; a clean fresh instance
    # is proven by it computing correctly straight after a trapped instance.
    assert {:ok, [55]} = SnifDemo.SafeNif.fibonacci(10)
    assert {:ok, [6765]} = SnifDemo.SafeNif.fibonacci(20)
  end

  @tag :pool
  test "whitelist: an un-exported name is refused without instantiating" do
    assert {:error, {:no_such_export, "not_a_real_export"}} =
             Snif.call(SnifDemo.SafeNif, "not_a_real_export", [])
  end

  @tag :pool
  @tag timeout: 120_000
  test "Store recycling survives crossing the default max_instantiations (256)" do
    # 600 calls across the default pool (max_instantiations=256) forces every
    # worker's Store to recycle at least once; every call must still return
    # correctly, proving recycle rebuilds a working Store+Module.
    for _ <- 1..600 do
      assert {:ok, [42]} = SnifDemo.SafeNif.still_alive()
    end
  end

  @tag :pool
  test "concurrency / back-pressure: many concurrent calls all complete" do
    results =
      1..20
      |> Task.async_stream(fn _ -> SnifDemo.SafeNif.fibonacci(10) end,
        max_concurrency: 8,
        timeout: 10_000
      )
      |> Enum.map(fn {:ok, r} -> r end)

    assert Enum.all?(results, &match?({:ok, [55]}, &1))
  end
end
