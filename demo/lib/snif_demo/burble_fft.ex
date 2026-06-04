# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
defmodule SnifDemo.BurbleFFT do
  @moduledoc """
  Burble FFT operations compiled to WASM for crash isolation.
  """

  @doc """
  Compute FFT using WASM-backed implementation.
  """
  def fft(wasm_path, signal) do
    SnifDemo.Loader.call(wasm_path, "fft", [length(signal)] ++ signal)
  end

  @doc """
  Compute IFFT using WASM-backed implementation.
  """
  def ifft(wasm_path, spectrum) do
    SnifDemo.Loader.call(wasm_path, "ifft", spectrum)
  end

  @doc """
  Test that BEAM survives FFT crashes.
  """
  def test_crash_isolation(wasm_path) do
    case fft(wasm_path, [1.0, 2.0, 3.0, 4.0]) do
      {:ok, result} -> {:ok, result}
      {:error, reason} -> 
        case SnifDemo.Loader.call(wasm_path, "still_alive", []) do
          {:ok, [42]} -> {:error, :crash_isolated, reason: reason}
          other -> {:error, :beam_died, detail: other}
        end
    end
  end
end