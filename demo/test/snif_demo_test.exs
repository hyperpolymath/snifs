# SPDX-License-Identifier: MPL-2.0
defmodule SnifDemoTest do
  use ExUnit.Case, async: false
  alias SnifDemo.Loader

  @safe  Path.join([__DIR__, "..", "..", "priv", "safe_nif_ReleaseSafe.wasm"])
  @fast  Path.join([__DIR__, "..", "..", "priv", "safe_nif_ReleaseFast.wasm"])

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

  test "ReleaseFast: oob reads canary from adjacent memory — DANGEROUS" do
    # In ReleaseFast the bounds check is stripped. The OOB read at index 3 of
    # `crash_layout.arr` lands on `crash_layout.canary` (0x0BADF00D) placed
    # adjacent by the extern-struct layout pin. The host gets a plausible-
    # looking value back with no indication anything is wrong — exactly the
    # silent-corruption mode SNIFS+ReleaseSafe is sold as eliminating, and
    # which this assertion proves is reintroduced underneath SNIFS if the
    # wasm guest gets built with safety checks stripped. A drift in this value
    # (or a {:error, _} here) means either Zig's data-segment layout changed
    # or — worse — the ReleaseFast artifact has somehow regained safety checks.
    assert {:ok, [195_948_557]} = Loader.call(@fast, "crash_oob", [])
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
