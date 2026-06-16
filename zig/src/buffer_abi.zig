// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// buffer_abi.zig — SNIF Buffer ABI v1: minimal working (ptr,len) linear-memory
// marshalling for crash-isolated BEAM NIFs.
//
// WHY THIS EXISTS
// ---------------
// The original burble_fft.zig exports `fn fft(data: []f32, n: usize)` — a SLICE
// parameter. Under the wasm32 `wasm_mvp` calling convention Zig REJECTS slice
// params ("parameter of type '[]f32' not allowed in function with calling
// convention 'wasm_mvp'"): WASM-MVP has no fat-pointer representation, so a
// (ptr,len) slice cannot be an export argument. This file implements the fix
// recommended by the buffer-abi design: hand-rolled (ptr,len) over WASM-MVP
// linear memory plus a guest-side bump allocator. Slices are LEGAL internally;
// they are reconstructed from a raw (ptr,len) INSIDE each export and never
// crossed the ABI boundary.
//
// COMPONENT-MODEL NOTE (deferred, per design)
// -------------------------------------------
// The design's option (b) — WebAssembly Component Model / WIT with `list<f32>`
// over the canonical ABI — is the right v2/v3 target once records/variants/
// strings proliferate. It is NOT used for v1: Zig 0.15 has no native
// component-model emit (it would require `wasm-tools component new` + a
// WASI-preview2 adapter + an authored .wit), it pulls in a far larger surface
// to verify, and it contradicts ADR-002 (wasm32-freestanding, no WASI). v1 is
// deliberately the simplest thing that builds today.
//
// BUILD INVARIANT (mirrors safe_nif.zig / the Justfile build-wasm recipe)
// ----------------------------------------------------------------------
// Compile with -OReleaseSafe: OOB on the rebuilt internal slice TRAPS (wasm
// `unreachable`), which the host surfaces as {:error, _}. -OReleaseFast strips
// the bounds check and turns OOB into a SILENT wrong answer — the ReleaseFast
// hazard class. Always ship ReleaseSafe. We build BOTH here only to exhibit the
// discrimination, exactly as safe_nif.zig does.
//
// ABI CONTRACT (language-agnostic; every future guest reimplements this surface)
// -----------------------------------------------------------------------------
// On wasm32 all pointers and usize are i32 at the WASM boundary, so:
//   snif_alloc(len: i32)            -> i32   byte-offset into linear `memory`, 0 = OOM
//   snif_dealloc(ptr: i32, len: i32)   -> void  (bump arena: only frees the most
//                                              recent allocation; see below)
//   snif_reset()                    -> void  reset arena to empty (per-call hook)
//   sum_f32(ptr: i32, len: i32)      -> f32   sum of `len` f32s at byte-offset ptr
//   scale_f32(ptr: i32, len: i32, k: f32) -> void  in-place multiply by k
// The linear memory itself is exported as `memory`, which is exactly what the
// host's Wasmex.Memory.{read_binary,write_binary} read/write against.

const std = @import("std");

// ── Bump arena ───────────────────────────────────────────────────────────────
// Fixed 1 MiB scratch in linear memory. No WASI, no libc, no general allocator.
// Deterministic for the proof obligations (Idris2 Compliance.idr fftBufValid /
// WasmArrayValid): a known fixed `memory` size and a 16-byte-aligned base.
//
// These globals live in LINEAR MEMORY (initialised by the module's data
// segment), NOT as mutable wasm (global) decls. A fresh instance re-runs the
// data segment, so re-instantiation is a correct no-shared-state reset — the
// pooled-worker (ADR-004 re-instantiate-per-call) model relies on this.
const ARENA_BYTES: usize = 1 << 20; // 1 MiB
var arena_buf: [ARENA_BYTES]u8 align(16) = [_]u8{0} ** ARENA_BYTES;
var arena_off: usize = 0;

/// Last allocation's start offset, so snif_dealloc can pop the most recent block
/// (a bump arena only supports LIFO free). 0 = no live allocation to pop.
var arena_last: usize = 0;

/// Reserve `len` bytes, 16-byte aligned (covers f32/i32/i64 alignment at once).
/// Returns the linear-memory byte offset of the block, or 0 on OOM.
/// 16-byte alignment is the host-side discharge of WasmArrayValid.baseAligned
/// (b mod 4 = 0 for F32) noted in the Idris obligations.
export fn snif_alloc(len: usize) usize {
    const a = std.mem.alignForward(usize, arena_off, 16);
    if (a + len > arena_buf.len) return 0; // OOM -> 0 (the "third outcome")
    arena_last = a;
    arena_off = a + len;
    return @intFromPtr(&arena_buf[a]);
}

/// LIFO free: if `ptr` is the most recent allocation, roll the bump pointer
/// back to it; otherwise this is a no-op (bump arenas cannot free in the
/// middle). `len` is accepted for ABI symmetry / future allocators.
export fn snif_dealloc(ptr: usize, len: usize) void {
    _ = len;
    if (ptr == 0) return;
    const base = @intFromPtr(&arena_buf[0]);
    if (ptr < base) return;
    const off = ptr - base;
    if (off == arena_last) {
        arena_off = arena_last;
        arena_last = 0;
    }
}

/// Reset the arena to empty. Call between SNIF invocations on a reused instance
/// (pairs with the host pool's per-call lifecycle).
export fn snif_reset() void {
    arena_off = 0;
    arena_last = 0;
}

// ── Buffer operations over (ptr,len) ─────────────────────────────────────────
// KEY RULE: slices may exist INTERNALLY; they may NEVER be export params
// (wasm_mvp rejects them — that is the whole bug we are fixing). Each export
// takes a raw (ptr,len) of i32s and rebuilds the slice itself.

/// Sum `len` consecutive f32 values starting at byte-offset `ptr`.
/// ptr==0 (the OOM sentinel / null) returns 0 without touching memory.
/// Under ReleaseSafe an out-of-bounds (ptr,len) traps when the rebuilt slice
/// is indexed; under ReleaseFast it would silently read adjacent memory.
export fn sum_f32(ptr: usize, len: usize) f32 {
    if (ptr == 0) return 0;
    const data: [*]f32 = @ptrFromInt(ptr);
    const xs = data[0..len]; // slice rebuilt INSIDE the guest (legal)
    var acc: f32 = 0;
    for (xs) |x| acc += x;
    return acc;
}

/// In-place: multiply each of `len` f32s at byte-offset `ptr` by `k`.
/// The "result" is the mutated buffer, read back by the host via the same ptr.
/// Returns nothing; ptr==0 is a no-op.
export fn scale_f32(ptr: usize, len: usize, k: f32) void {
    if (ptr == 0) return;
    const data: [*]f32 = @ptrFromInt(ptr);
    const xs = data[0..len];
    for (xs) |*x| x.* *= k;
}

// ── Liveness / mode-discrimination witnesses ─────────────────────────────────

/// Always-true liveness probe (the buffer-ABI analogue of safe_nif.still_alive).
export fn still_alive() i32 {
    return 1;
}

/// Deliberate out-of-bounds read over a buffer: rebuilds a slice of `len`+1
/// elements but indexes element `len` (one past). ReleaseSafe TRAPS; ReleaseFast
/// returns a silent wrong value — exhibits the safety discrimination on the
/// BUFFER path (not just the scalar path), matching the eval's anti-property.
export fn crash_oob_buffer(ptr: usize, len: usize) f32 {
    if (ptr == 0) return 0;
    const data: [*]f32 = @ptrFromInt(ptr);
    const xs = data[0..len];
    var idx: usize = len; // one past the end — runtime value, not comptime
    if (xs.len == 0) idx = 0;
    return xs[idx]; // ReleaseSafe: trap; ReleaseFast: silent read
}
