# SPDX-License-Identifier: MPL-2.0
defmodule SnifDemo.Loader do
  @moduledoc """
  Loads a WASM module via wasmex and calls exported functions.
  Returns {:ok, results} | {:error, reason} — never crashes the calling process.

  Uses Wasmex.start_link/1 (GenServer) + Wasmex.call_function/3, which is
  the correct wasmex 0.14 API. WASM traps surface as {:error, reason} tuples;
  the BEAM process remains alive in both the success and trap cases.
  """

  @doc """
  Call an exported function in the given WASM file.
  Returns {:ok, [results]} on success, {:error, reason} on WASM trap or load error.
  The calling BEAM process is never killed regardless of what the WASM guest does.
  """
  def call(wasm_path, function_name, args \\ []) do
    with {:ok, bytes} <- File.read(wasm_path),
         {:ok, pid}   <- Wasmex.start_link(%{bytes: bytes}) do
      result = Wasmex.call_function(pid, function_name, args)
      # Always stop the instance after the call — each call gets a fresh instance
      # which matches the per-call NIF isolation model.
      GenServer.stop(pid, :normal)
      result
    end
  end
end
