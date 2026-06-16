// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// snif-logic: ALL verifiable business logic for the Rust SNIF guest.
//
// #![forbid(unsafe_code)] is GENUINE here (verified: it rejects even an
// #[allow(unsafe_code)]-wrapped unsafe block, E0453). This is the crate the
// source verifier proves. It has NO exports, NO #[no_mangle], NO raw memory:
// it operates only on owned values and borrowed slices the guest hands it.
//
// Verifier-on-by-default (owner directive): the Kani harnesses below run as a
// standard CI build step (`cargo kani`). They are no-ops in a normal build.
#![no_std]
#![forbid(unsafe_code)]

/// Iterative Fibonacci. Mirrors safe_nif.zig `fibonacci`.
pub fn fib(n: i32) -> i64 {
    if n <= 0 {
        return 0;
    }
    let (mut a, mut b): (i64, i64) = (0, 1);
    let mut i = 1;
    while i < n {
        let t = a + b; // overflow-checks=true makes this trap past fib(92)
        a = b;
        b = t;
        i += 1;
    }
    b
}

/// Total addition. Returns None on overflow; the GUEST layer decides to trap.
/// Contrast safe_nif.zig `checked_add` which uses wrapping `+%`; the Rust SNIF
/// is STRICTER — it surfaces overflow as a trap rather than wrapping silently.
pub fn checked_add(a: i32, b: i32) -> Option<i32> {
    a.checked_add(b)
}

/// Buffer kernel: sum a borrowed f32 slice. The guest builds the slice from a
/// vetted linear-memory region; this function never touches raw pointers.
pub fn sum_f32(xs: &[f32]) -> f32 {
    let mut acc = 0.0f32;
    for &x in xs {
        acc += x;
    }
    acc
}

/// In-place buffer kernel: scale every element. Borrowed mut slice, no unsafe.
pub fn scale_f32(xs: &mut [f32], k: f32) {
    for x in xs.iter_mut() {
        *x *= k;
    }
}

// ── Verifier harnesses (Kani). Run by `cargo kani --features verify`. ──
// These are PROOF obligations discharged at CI time, not runtime asserts.
#[cfg(kani)]
mod proofs {
    use super::*;

    // checked_add never returns a wrong Some: if it is Some(v) then v == a+b
    // over the integers (no wrap). Kani explores all i32 x i32.
    #[kani::proof]
    fn checked_add_is_exact_or_none() {
        let a: i32 = kani::any();
        let b: i32 = kani::any();
        match checked_add(a, b) {
            Some(v) => assert!((a as i64) + (b as i64) == v as i64),
            None => assert!((a as i64) + (b as i64) > i32::MAX as i64
                || (a as i64) + (b as i64) < i32::MIN as i64),
        }
    }

    // sum_f32 of a length-0 slice is 0.0 (boundary the buffer ABI relies on).
    #[kani::proof]
    fn sum_empty_is_zero() {
        let xs: [f32; 0] = [];
        assert!(sum_f32(&xs) == 0.0);
    }
}
