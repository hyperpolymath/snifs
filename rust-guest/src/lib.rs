// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// rust-guest — a MINIMAL Rust->wasm32 SNIF guest (no_std, cdylib).
//
// Exports (all wasm i32/i64/f32 scalars on wasm32; ZERO host imports):
//   checked_add_i32(i32, i32) -> i32   STRICT: traps on overflow
//   sum_f32(ptr: i32, n: i32) -> f32   Buffer ABI: sum n f32s at `ptr`
//   snif_alloc(i32) -> i32             Buffer ABI: bump-allocate scratch
//   still_alive() -> i32               liveness control (returns 42)
//   memory                             the exported linear memory (auto-emitted)
//
// SAFETY MODEL (see Cargo.toml for the rustc-1.95 forbid/no_mangle finding):
//   - crate-level  #![deny(unsafe_code)]   — overridable per-item, only for the
//                                            export attribute.
//   - `logic`      #![forbid(unsafe_code)] — pure arithmetic; the verifier's
//                                            target; unsafe is IMPOSSIBLE here.
//   - `abi`        the ONLY linear-memory unsafe, one audited per-item #[allow].
//
// HONESTY: these exports prove the ABI/value model only. The OPERATIONAL SNIF
// theorem (guest trap => {:error, _} AND the BEAM survives, over real WASM
// semantics) is TESTED at the host, NOT proven here. This guest is "Safer",
// not "Safe" — it inherits the Zig guest's isolation story exactly.

#![no_std]
#![deny(unsafe_code)]

use core::panic::PanicInfo;

// A Rust panic in a SNIF MUST become a wasm trap (caught by the host), never an
// unwind. panic="abort" (profile) + this handler guarantee it. Verified shape:
// `checked_add_i32(i32::MAX, 1)` -> "wasm unreachable instruction executed".
#[panic_handler]
fn panic_to_trap(_: &PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

// ── Pure, verifiable logic — the crate the verifier proves ────────────────
// `#![forbid(unsafe_code)]` here has real teeth: no raw memory, no exports, so
// `forbid` does not collide with the `no_mangle`-is-unsafe rule. This mirrors
// the design's `snif-logic` crate (the Creusot/Kani target).
mod logic {
    #![forbid(unsafe_code)]

    /// Total addition; `None` on i32 overflow. The export turns `None` into a
    /// trap, making this STRICTER than Zig's wrapping `+%` checked_add.
    pub const fn checked_add_i32(a: i32, b: i32) -> Option<i32> {
        a.checked_add(b)
    }

    /// Sum a slice of f32 (slices are legal INTERNALLY; never as wasm params).
    pub fn sum_f32(xs: &[f32]) -> f32 {
        let mut acc = 0.0f32;
        let mut i = 0usize;
        while i < xs.len() {
            acc += xs[i];
            i += 1;
        }
        acc
    }
}

// ── Linear-memory ABI — the single audited unsafe surface ─────────────────
// One `#[allow(unsafe_code)]` block. Reads outside the guest's linear memory
// are bounds-checked by the engine and TRAP (verified upstream: an OOB region
// surfaces as "out of bounds memory access" caught by the host).
mod abi {
    use core::alloc::{GlobalAlloc, Layout};

    // Fixed 1 MiB bump arena. Never frees — SOUND ONLY under the SNIF pool's
    // re-instantiate-per-call model (ADR-004): each call gets a fresh linear
    // memory, resetting the arena for free. Swap to lol_alloc/dlmalloc for any
    // in-place-reuse model (the production note from ADR-0005).
    const ARENA_LEN: usize = 1 << 20;
    static mut ARENA: [u8; ARENA_LEN] = [0; ARENA_LEN];
    static mut OFFSET: usize = 0;

    /// Reserve `len` bytes, 16-byte aligned (so F32/I32/I64 bases all align).
    /// Returns a linear-memory byte offset, or 0 on OOM (a recognised THIRD
    /// outcome alongside ok/trap — the ternary-fidelity gap the audit flagged).
    #[allow(unsafe_code)]
    pub fn alloc(len: usize) -> usize {
        unsafe {
            let base = core::ptr::addr_of!(ARENA) as usize;
            let off = (OFFSET + 15) & !15usize;
            if off + len > ARENA_LEN {
                return 0;
            }
            OFFSET = off + len;
            base + off
        }
    }

    /// Borrow `n` f32s at byte offset `ptr` as a slice. An out-of-arena or
    /// out-of-memory region is bounds-checked by the engine and traps.
    #[allow(unsafe_code)]
    pub fn read_f32s<'a>(ptr: usize, n: usize) -> &'a [f32] {
        unsafe { core::slice::from_raw_parts(ptr as *const f32, n) }
    }

    pub struct Bump;
    #[allow(unsafe_code)]
    unsafe impl GlobalAlloc for Bump {
        unsafe fn alloc(&self, l: Layout) -> *mut u8 {
            let p = alloc(l.size());
            p as *mut u8
        }
        unsafe fn dealloc(&self, _p: *mut u8, _l: Layout) {}
    }
}

// no_std cdylib needs a global allocator to link. The bump arena above doubles
// as it (the only consumer is the engine's own machinery; our exports use the
// arena directly via abi::alloc).
#[global_allocator]
static GLOBAL: abi::Bump = abi::Bump;

// ── Exports (the host-facing SNIF surface) ────────────────────────────────
// Each `#[unsafe(no_mangle)]` carries a per-item #[allow(unsafe_code)] for the
// ATTRIBUTE only (rustc-1.95 classifies `no_mangle` under unsafe_code); the
// bodies contain no unsafe and delegate to `logic`/`abi`.

/// STRICT checked add: traps (via panic -> unreachable) on i32 overflow.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub extern "C" fn checked_add_i32(a: i32, b: i32) -> i32 {
    match logic::checked_add_i32(a, b) {
        Some(v) => v,
        None => panic!("checked_add_i32 overflow"),
    }
}

/// Buffer ABI: bump-allocate `len` bytes; returns offset (0 = OOM).
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub extern "C" fn snif_alloc(len: i32) -> i32 {
    if len < 0 {
        return 0;
    }
    abi::alloc(len as usize) as i32
}

/// Buffer ABI: sum `n` f32s starting at byte offset `ptr` in linear memory.
/// OOB region => engine bounds-check trap (caught by the host).
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub extern "C" fn sum_f32(ptr: i32, n: i32) -> f32 {
    if ptr < 0 || n < 0 {
        return 0.0;
    }
    logic::sum_f32(abi::read_f32s(ptr as usize, n as usize))
}

/// Liveness control: a fresh instance always answers 42.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub extern "C" fn still_alive() -> i32 {
    42
}
