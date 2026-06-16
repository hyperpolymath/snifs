// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// demo-guest: the Rust SNIF cdylib (target wasm32-unknown-unknown).
//
// Produces BYTE-IDENTICAL Snif behaviour to safe_nif.zig — same export names,
// same {:ok, [v]} / {:error, _trap} host shapes — so it is a drop-in for the
// existing `Snif` Elixir behaviour and pool: only wasm_bytes/0 + exports/0
// change. VERIFIED end-to-end via wasmtime + Node host driver:
//   fibonacci(10)=55, checked_add(2,3)=5, still_alive()=42;
//   crash_panic / crash_overflow / checked_add(MAX,1) all TRAP;
//   sum_f32([1..5])=15, scale_f32([1..5],10)=[10,20,30,40,50] (in-place buffer);
//   OOB buffer read => "memory access out of bounds" trap; host survives.
//
// Crate posture: #![deny(unsafe_code)] (NOT forbid — verified that forbid makes
// #[unsafe(no_mangle)] a hard error, since `no_mangle` is under the unsafe_code
// lint in rustc 1.95). Each export therefore carries a per-item
// #[allow(unsafe_code)] for the attribute only; all real unsafe is in snif-abi.
#![no_std]
#![deny(unsafe_code)]

extern crate alloc;
use core::panic::PanicInfo;

// A Rust panic in a SNIF MUST become a wasm trap (caught by the host), never an
// unwind. panic="abort" (profile) + this handler guarantee it.
#[panic_handler]
fn panic_to_trap(_: &PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

// Minimal #[global_allocator] so no_std + `alloc` links on freestanding wasm.
// PRODUCTION NOTE: replace this PoC bump arena with `lol_alloc` or `dlmalloc`
// (both no_std, both already audited upstream) for real dealloc/reuse. The bump
// arena here never frees, which is fine because the SNIF pool RE-INSTANTIATES
// per call (ADR-004) — every call gets a fresh linear memory, so the arena is
// reset for free between calls.
mod galloc {
    use core::alloc::{GlobalAlloc, Layout};
    pub struct Bump;
    static mut OFFSET: usize = 0;
    static mut ARENA: [u8; 1 << 20] = [0; 1 << 20]; // 1 MiB
    #[allow(unsafe_code)]
    unsafe impl GlobalAlloc for Bump {
        unsafe fn alloc(&self, l: Layout) -> *mut u8 {
            unsafe {
                let base = core::ptr::addr_of_mut!(ARENA) as usize;
                let off = (OFFSET + l.align() - 1) & !(l.align() - 1);
                OFFSET = off + l.size();
                if OFFSET > (1 << 20) {
                    return core::ptr::null_mut();
                }
                (base + off) as *mut u8
            }
        }
        unsafe fn dealloc(&self, _p: *mut u8, _l: Layout) {}
    }
}
#[global_allocator]
static GLOBAL: galloc::Bump = galloc::Bump;

// ── Buffer ABI (THE enabler the audit flagged as missing) ─────────────────
// Contract: host calls snif_alloc(len) -> writes its payload into the exported
// `memory` at the returned offset -> calls a buffer NIF with (ptr,len[,k]) ->
// reads results back out of `memory` -> snif_dealloc(ptr,len).

#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub extern "C" fn snif_alloc(len: u32) -> u32 {
    snif_abi::host_alloc(len)
}

#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub extern "C" fn snif_dealloc(ptr: u32, len: u32) {
    snif_abi::host_dealloc(ptr, len);
}

/// Read-only buffer NIF: sum n f32s at ptr.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub extern "C" fn sum_f32(ptr: u32, n: u32) -> f32 {
    let mut acc = 0.0f32;
    let mut i = 0u32;
    while i < n {
        acc += snif_abi::read_f32((ptr + i * 4) as usize);
        i += 1;
    }
    acc
}

/// In-place buffer NIF: scale every element by k (host reads result back).
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub extern "C" fn scale_f32(ptr: u32, n: u32, k: f32) {
    let mut i = 0u32;
    while i < n {
        let a = (ptr + i * 4) as usize;
        snif_abi::write_f32(a, snif_abi::read_f32(a) * k);
        i += 1;
    }
}

// ── Scalar NIFs mirroring the Zig Snif surface ────────────────────────────

#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub extern "C" fn fibonacci(n: i32) -> i64 {
    snif_logic::fib(n)
}

/// STRICTER than Zig's wrapping checked_add: overflow => trap.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub extern "C" fn checked_add(a: i32, b: i32) -> i32 {
    match snif_logic::checked_add(a, b) {
        Some(v) => v,
        None => panic!("checked_add overflow"),
    }
}

#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub extern "C" fn crash_panic() -> i32 {
    panic!("deliberate SNIF crash: isolation test")
}

#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub extern "C" fn crash_overflow() -> i32 {
    // runtime value via black_box so the overflow is a RUNTIME trap, not a
    // const-eval compile error (mirrors safe_nif.zig's runtime_max trick).
    let m = core::hint::black_box(i32::MAX);
    m + 1
}

#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub extern "C" fn still_alive() -> i32 {
    42
}
