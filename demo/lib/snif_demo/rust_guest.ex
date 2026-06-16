# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
defmodule SnifDemo.RustGuest do
  @moduledoc """
  A Rust SNIF guest (rust/crates/demo-guest, compiled to wasm32-unknown-unknown).

  This module is the PROOF that the SNIF `Snif` behaviour is guest-language
  agnostic: it implements EXACTLY the same callbacks as a Zig guest would, the
  only differences being `wasm_bytes/0` (points at the Rust artifact) and the
  `exports/0` whitelist (adds the Buffer ABI). The pool, isolation, no-shared-
  state, and liveness machinery are unchanged.

  The Rust guest is STRICTER than the Zig one in one respect: `checked_add`
  TRAPS on overflow (the Zig demo wraps with `+%`). Both are valid SNIFs; the
  Rust one demonstrates verifier-on-by-default making the safe choice the
  default choice.

  ## Buffer ABI

  Scalar exports take plain numbers. Buffer exports take a `(ptr, len)` pair into
  the guest's linear memory; the host marshals through `snif_alloc/1` +
  `snif_dealloc/2`. See `call_buffer_f32/3`.
  """
  @behaviour Snif

  @wasm_path Path.join([__DIR__, "..", "..", "..", "rust", "target",
               "wasm32-unknown-unknown", "release", "demo_guest.wasm"])

  @impl Snif
  def wasm_bytes, do: File.read(@wasm_path)

  @impl Snif
  def exports do
    [
      # scalar NIFs (same surface as the Zig guest)
      {"fibonacci", 1},
      {"checked_add", 2},
      {"crash_panic", 0},
      {"crash_overflow", 0},
      {"still_alive", 0},
      # Buffer ABI
      {"snif_alloc", 1},
      {"snif_dealloc", 2},
      {"sum_f32", 2},
      {"scale_f32", 3}
    ]
  end

  @impl Snif
  # Bounded fuel = the liveness/DoS guard (ADR-004). A runaway Rust guest traps.
  def fuel_per_call, do: 50_000_000

  @impl Snif
  # 16 MiB store cap; the guest's own arena is 1 MiB but linear memory may grow.
  def memory_limit_bytes, do: 16 * 1024 * 1024

  # ── Buffer ABI convenience wrappers (host-side marshalling) ──────────────
  #
  # These show the (ptr,len) round-trip the host performs. They run on a single
  # pooled instance so the alloc + op + readback share one linear memory.
  # NOTE: needs the wasmex memory read/write API on the live instance; sketched
  # here against `Wasmex.Memory` (wasmex 0.14). The shape, not the exact call,
  # is the load-bearing part for this design.

  @doc """
  Sum a list of f32 in the Rust guest via the Buffer ABI.

  Marshalling: snif_alloc(n*4) -> write f32s into linear memory at ptr ->
  sum_f32(ptr, n) -> snif_dealloc(ptr, n*4). Returns `{:ok, [sum]}` or an
  isolated `{:error, _}` (e.g. an OOB region traps and is caught).
  """
  @spec sum_f32([float()], keyword()) :: Snif.result()
  def sum_f32(floats, opts \\ []) do
    Snif.Pool.with_instance(__MODULE__, opts, fn instance, store ->
      n = length(floats)
      with {:ok, [ptr]} when ptr != 0 <- call(instance, store, "snif_alloc", [n * 4]) do
        :ok = write_f32s(instance, store, ptr, floats)
        result = call(instance, store, "sum_f32", [ptr, n])
        _ = call(instance, store, "snif_dealloc", [ptr, n * 4])
        result
      end
    end)
  end

  # The following two helpers are the wasmex 0.14 memory-marshalling shape.
  # Wasmex.Instance.memory/2 -> %Wasmex.Memory{}; Wasmex.Memory.write_binary/4
  # and read_binary/4 move bytes in/out of linear memory at a byte offset.
  defp write_f32s(instance, store, ptr, floats) do
    bin = for f <- floats, into: <<>>, do: <<f::float-32-little>>
    {:ok, mem} = Wasmex.Instance.memory(store, instance)
    Wasmex.Memory.write_binary(store, mem, ptr, bin)
  end

  # Synchronous call against the LIVE transaction instance. Uses the verified
  # wasmex 0.14 reply wire-shape: pass `from = {self(), ref}`; the NIF sends
  # `{ref, {:ok,[..]} | {:error, bin}}` back (native/wasmex/src/instance.rs).
  defp call(instance, store, fun, args, timeout \\ 5_000) do
    ref = make_ref()

    case Wasmex.Instance.call_exported_function(store, instance, fun, args, {self(), ref}) do
      :ok ->
        receive do
          {^ref, result} -> result
        after
          timeout -> {:error, {:timeout, timeout}}
        end

      {:error, _} = err ->
        err
    end
  end
end
