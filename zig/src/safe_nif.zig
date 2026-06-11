// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// safe_nif.zig — SNIF demo: Zig functions compiled to WASM for crash-isolated BEAM NIFs.
//
// Compile with ReleaseSafe: all safety violations become WASM unreachable traps,
// catchable by the host runtime (wasmex/wasmtime). The BEAM VM survives every trap.
//
// Compile with ReleaseFast: UB collapses to silent wrong answers (not crashes) —
// demonstrates WHY ReleaseSafe is the only correct mode for SNIFs.

const std = @import("std");

// Prevent comptime evaluation of runtime values used in failure demos
var runtime_index: usize = 3;
var runtime_zero: i32 = 0;
var runtime_max: i32 = std.math.maxInt(i32);

// Layout-pinned crash demo: extern struct forces declaration-order field
// placement, so an OOB read at index 3 of `arr` deterministically lands on
// `canary` rather than indeterminate stack/heap memory. Under ReleaseSafe the
// bounds check fires before the load; under ReleaseFast the check is stripped
// and the load returns 0x0BADF00D — a recognisable wrong answer instead of an
// ambiguous zero that could equally mean "load was DCE'd" or "read 0 from
// adjacent memory."
const CrashLayout = extern struct {
    arr: [3]i32,
    canary: i32,
};
var crash_layout: CrashLayout = .{
    .arr = .{ 10, 20, 30 },
    .canary = 0x0BADF00D,
};

// --- Safe computation (would be a real NIF use-case) ---

/// Iterative fibonacci — no safety issues, just a useful computation.
/// Demonstrates that the WASM/wasmex path has acceptable overhead.
export fn fibonacci(n: i32) i64 {
    if (n <= 0) return 0;
    if (n == 1) return 1;
    var a: i64 = 0;
    var b: i64 = 1;
    var i: i32 = 2;
    while (i <= n) : (i += 1) {
        const tmp = a + b;
        a = b;
        b = tmp;
    }
    return b;
}

/// Safe integer addition with overflow check.
/// In ReleaseSafe: overflow -> trap. In ReleaseFast: wraps silently.
export fn checked_add(a: i32, b: i32) i32 {
    return a +% b; // Use wrapping add explicitly — this is intentional
}

// --- Crash isolation demos ---

/// OOB array access via runtime index.
/// ReleaseSafe: bounds check -> unreachable trap.
/// ReleaseFast: bounds check stripped -> reads `crash_layout.canary` adjacent
/// in linear memory, returns 0x0BADF00D (195948557) silently. The distinctive
/// value distinguishes real silent corruption from the load being eliminated.
export fn crash_oob() i32 {
    return crash_layout.arr[runtime_index]; // runtime_index = 3, one past end
}

/// Explicit unreachable — always reached at runtime.
/// ALL modes: emits WASM unreachable instruction -> trap.
export fn crash_unreachable() i32 {
    if (runtime_index == 99) unreachable;
    return 0;
}

/// @panic — always panics.
/// ALL modes: emits WASM unreachable instruction -> trap.
export fn crash_panic() i32 {
    @panic("deliberate SNIF crash: isolation test");
}

/// Integer overflow.
/// ReleaseSafe: overflow -> trap.
/// ReleaseFast: wrapping arithmetic, returns wrong value silently.
export fn crash_overflow() i32 {
    return runtime_max + 1;
}

/// Divide by zero.
/// ReleaseSafe: divExact checks for zero -> trap.
/// ReleaseFast: optimizer removes operation, returns 0 silently.
export fn crash_div_zero() i32 {
    return @divExact(100, runtime_zero);
}

// --- Control case ---

/// Always returns 42. Used to verify BEAM is still alive after traps.
export fn still_alive() i32 {
    return 42;
}
