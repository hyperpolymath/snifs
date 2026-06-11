# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
defmodule BurbleFFTTest do
  use ExUnit.Case, async: false
  alias SnifDemo.BurbleFFT
  alias SnifDemo.Loader

  @fft_wasm Path.join([__DIR__, "../../", "priv", "safe_nif_ReleaseSafe.wasm"])

  # ── Basic FFT functionality ────────────────────────────────────────────────

  test "still_alive returns 42" do
    assert {:ok, [42]} = Loader.call(@fft_wasm, "still_alive", [])
  end

  # ── Crash Isolation ───────────────────────────────────────────────────

  test "BEAM survives OOB crash" do
    assert {:error, _trap} = Loader.call(@fft_wasm, "crash_oob", [])
    # Critical assertion: BEAM process is still alive
    assert {:ok, [42]} = Loader.call(@fft_wasm, "still_alive", [])
  end

  # Note: Actual FFT computation would require proper memory setup
  # This is a minimal demonstration of the crash isolation principle
  
  test "WASM module can be called multiple times" do
    # Multiple calls to verify stability
    assert {:ok, [42]} = Loader.call(@fft_wasm, "still_alive", [])
    assert {:ok, [42]} = Loader.call(@fft_wasm, "still_alive", [])
    assert {:ok, [42]} = Loader.call(@fft_wasm, "still_alive", [])
  end

  # ── Integration Test ──────────────────────────────────────────────────────

  test "BurbleFFT module can call WASM functions" do
    result = BurbleFFT.test_crash_isolation(@fft_wasm)
    # Should either succeed or return crash_isolated error
    case result do
      {:ok, _} -> assert true  # Call worked
      {:error, :crash_isolated, reason: _} -> assert true  # Crash was isolated
      {:error, :beam_died, detail: _} -> flunk("BEAM process died")
    end
  end
end