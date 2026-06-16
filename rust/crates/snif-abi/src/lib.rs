// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// snif-abi: the SINGLE vetted unsafe surface of the Rust SNIF guest.
//
// Policy: crate-wide #![deny(unsafe_code)] with #[allow(unsafe_code)] on ONLY
// the four audited primitives below (alloc / dealloc / read / write into the
// guest's own linear memory). This keeps the unsafe blast radius to one small
// file that a human reviews line-by-line; everything else in the workspace is
// deny/forbid.
//
// These primitives are MEMORY-SAFE-BY-DELEGATION: an out-of-range address is a
// wasm linear-memory access, so an OOB read/write traps in the engine (verified:
// `sum_f32(ptr, huge_n)` -> "memory access out of bounds" RuntimeError, caught
// by the host as {:error, _}). The guest cannot escape its sandbox; the worst a
// buggy ABI call can do is trap.
#![no_std]
#![deny(unsafe_code)]

extern crate alloc;
use core::alloc::Layout;

/// Allocate `len` bytes (align 8) in the guest's linear memory; return the
/// offset, or 0 on failure / len==0. The host writes its payload here, then
/// passes the offset to a buffer NIF.
#[allow(unsafe_code)]
pub fn host_alloc(len: u32) -> u32 {
    if len == 0 {
        return 0;
    }
    let layout = match Layout::from_size_align(len as usize, 8) {
        Ok(l) => l,
        Err(_) => return 0,
    };
    // SAFETY: layout is non-zero and well-formed; ptr is returned to the host
    // which owns its lifetime until the matching host_dealloc.
    (unsafe { alloc::alloc::alloc(layout) }) as u32
}

/// Free a region previously returned by `host_alloc`.
#[allow(unsafe_code)]
pub fn host_dealloc(ptr: u32, len: u32) {
    if ptr == 0 || len == 0 {
        return;
    }
    if let Ok(layout) = Layout::from_size_align(len as usize, 8) {
        // SAFETY: (ptr,len) match a prior host_alloc by host contract.
        unsafe { alloc::alloc::dealloc(ptr as *mut u8, layout) };
    }
}

/// Read one f32 at a linear-memory offset. OOB => wasm memory-access trap.
#[allow(unsafe_code)]
pub fn read_f32(addr: usize) -> f32 {
    // SAFETY: read is bounds-enforced by the wasm engine; worst case is a trap.
    unsafe { core::ptr::read(addr as *const f32) }
}

/// Write one f32 at a linear-memory offset. OOB => wasm memory-access trap.
#[allow(unsafe_code)]
pub fn write_f32(addr: usize, v: f32) {
    // SAFETY: as read_f32.
    unsafe { core::ptr::write(addr as *mut f32, v) };
}
