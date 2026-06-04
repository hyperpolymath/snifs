# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
defmodule SnifDemoTest do
  use ExUnit.Case, async: false
  alias SnifDemo.Loader

  @safe  Path.join([__DIR__, "..", "priv", "safe_nif_ReleaseSafe.wasm"])
  @fast  Path.join([__DIR__, "..", "priv", "safe_nif_ReleaseFast.wasm"])

  # ── Core isolation claim ──────────────────────────────────────────────────

  test "fibonacci(10) returns 55 — WASM path is functional" do
    assert {:ok, [55]} = Loader.call(@safe, "fibonacci", [10])
  end

  test "still_alive() returns 42 — baseline" do
    assert {:ok, [42]} = Loader.call(@safe, "still_alive", [])
  end

  test "BEAM survives oob trap and still_alive() works after" do
    assert {:error, _trap} = Loader.call(@safe, "crash_oob", [])
    # The critical assertion: the BEAM process is still running
    assert {:ok, [42]} = Loader.call(@safe, "still_alive", [])
  end

  test "BEAM survives unreachable trap and still_alive() works after" do
    assert {:error, _trap} = Loader.call(@safe, "crash_unreachable", [])
    assert {:ok, [42]} = Loader.call(@safe, "still_alive", [])
  end

  test "BEAM survives @panic trap and still_alive() works after" do
    assert {:error, _trap} = Loader.call(@safe, "crash_panic", [])
    assert {:ok, [42]} = Loader.call(@safe, "still_alive", [])
  end

  test "BEAM survives overflow trap and still_alive() works after" do
    assert {:error, _trap} = Loader.call(@safe, "crash_overflow", [])
    assert {:ok, [42]} = Loader.call(@safe, "still_alive", [])
  end

  test "BEAM survives div-zero trap and still_alive() works after" do
    assert {:error, _trap} = Loader.call(@safe, "crash_div_zero", [])
    assert {:ok, [42]} = Loader.call(@safe, "still_alive", [])
  end

  # ── ReleaseFast silent-wrong-answer demonstration ────────────────────────

  test "ReleaseFast: oob returns silent 0 instead of trapping — DANGEROUS" do
    # In ReleaseFast the optimizer removes the OOB access entirely.
    # The BEAM survives (no crash) but gets a wrong answer with no indication.
    result = Loader.call(@fast, "crash_oob", [])
    # Should NOT be {:error, _} — it succeeds silently with garbage
    assert {:ok, _} = result
    IO.puts("\n  [ReleaseFast oob result: #{inspect(result)}] — wrong answer, no trap")
  end

  test "ReleaseFast: unreachable still traps even in fast mode" do
    # unreachable is a first-class WASM instruction — optimizer cannot remove it
    assert {:error, _trap} = Loader.call(@fast, "crash_unreachable", [])
  end

  test "ReleaseFast: @panic still traps even in fast mode" do
    assert {:error, _trap} = Loader.call(@fast, "crash_panic", [])
  end

  # ── Multiple sequential crashes — stress test isolation ──────────────────

  test "five sequential traps, BEAM alive throughout" do
    crashes = [:crash_oob, :crash_unreachable, :crash_panic, :crash_overflow, :crash_div_zero]

    Enum.each(crashes, fn fn_name ->
      {:error, _} = Loader.call(@safe, to_string(fn_name), [])
    end)

    assert {:ok, [42]} = Loader.call(@safe, "still_alive", [])
  end
end
