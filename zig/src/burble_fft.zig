// SPDX-License-Identifier: MPL-2.0
// Burble FFT implementation for SNIF demonstration
// Compiles to WASM for crash-isolated DSP operations

const std = @import("std");
const math = std.math;

// Prevent comptime evaluation for runtime safety demos
var runtime_index: usize = 99;

//==============================================================================
// FFT Implementation (Cooley-Tukey radix-2 DIT)
//==============================================================================

/// In-place FFT on interleaved complex data.
/// data: [re0, im0, re1, im1, ...]
/// n: number of complex samples (must be power of 2)
export fn fft(data: []f32, n: usize) void {
    bit_reverse_permute(data, n);
    
    var stage: usize = 1;
    while (stage < n) : (stage *= 2) {
        const half_stage = stage;
        const angle_step = -math.pi / @as(f32, @floatFromInt(half_stage));
        
        var group: usize = 0;
        while (group < n) : (group += stage * 2) {
            var k: usize = 0;
            while (k < half_stage) : (k += 1) {
                const angle = angle_step * @as(f32, @floatFromInt(k));
                const wr = @cos(angle);
                const wi = @sin(angle);
                
                const even_idx = (group + k) * 2;
                const odd_idx = (group + k + half_stage) * 2;
                
                const er = data[even_idx];
                const ei = data[even_idx + 1];
                const or_ = data[odd_idx];
                const oi = data[odd_idx + 1];
                
                // Twiddle factor multiplication
                const tr = wr * or_ - wi * oi;
                const ti = wr * oi + wi * or_;
                
                data[even_idx] = er + tr;
                data[even_idx + 1] = ei + ti;
                data[odd_idx] = er - tr;
                data[odd_idx + 1] = ei - ti;
            }
        }
    }
}

/// In-place inverse FFT
export fn ifft(data: []f32, n: usize) void {
    // Conjugate input
    var i: usize = 1;
    while (i < data.len) : (i += 2) {
        data[i] = -data[i];
    }
    
    fft(data, n);
    
    // Conjugate and scale output
    const scale = 1.0 / @as(f32, @floatFromInt(n));
    i = 0;
    while (i < data.len) : (i += 2) {
        data[i] *= scale;
        data[i + 1] = -data[i + 1] * scale;
    }
}

/// Bit-reversal permutation for in-place FFT
fn bit_reverse_permute(data: []f32, n: usize) void {
    var j: usize = 0;
    for (0..n) |i| {
        if (i < j) {
            // Swap complex pair (i, j)
            std.mem.swap(f32, &data[i * 2], &data[j * 2]);
            std.mem.swap(f32, &data[i * 2 + 1], &data[j * 2 + 1]);
        }
        var m = n >> 1;
        while (m >= 1 and j >= m) : (m >>= 1) {
            j -= m;
        }
        j += m;
    }
}

//==============================================================================
// Crash Isolation Demos (for testing SNIF safety)
//==============================================================================

/// Deliberately crash with OOB access
export fn crash_oob_fft() i32 {
    const arr = [_]f32{ 1.0, 0.0, 0.0, 0.0 };
    return @intFromFloat(arr[runtime_index]); // OOB access
}

/// Always returns 42 to verify BEAM is alive
export fn still_alive() i32 {
    return 42;
}

//==============================================================================
// Helper for Elixir interop
//==============================================================================

/// Simple test function that returns a constant
export fn test_constant() f32 {
    return 3.14159;
}