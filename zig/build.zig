// SPDX-License-Identifier: MPL-2.0
const std = @import("std");

pub fn build(b: *std.Build) void {
    const modes = .{
        .{ "ReleaseSafe", .ReleaseSafe },
        .{ "ReleaseFast", .ReleaseFast },
    };

    const exports = [_][]const u8{
        "fibonacci", "checked_add", "crash_oob", "crash_unreachable",
        "crash_panic", "crash_overflow", "crash_div_zero", "still_alive",
    };

    const fft_exports = [_][]const u8{
        "fft", "ifft", "crash_oob_fft", "still_alive", "test_constant",
    };

    // Build original SNIF demos
    inline for (modes) |mode| {
        const name = "safe_nif_" ++ mode[0];
        const exe = b.addExecutable(.{
            .name = name,
            .root_source_file = b.path("src/safe_nif.zig"),
            .target = b.resolveTargetQuery(.{
                .cpu_arch = .wasm32,
                .os_tag = .freestanding,
            }),
            .optimize = mode[1],
        });
        exe.entry = .disabled;
        for (exports) |exp| exe.rdynamic = true;
        _ = exports;
        b.installArtifact(exe);
    }

    // Build Burble FFT SNIF
    const burble_fft = b.addExecutable(.{
        .name = "burble_fft",
        .root_source_file = b.path("src/burble_fft.zig"),
        .target = b.resolveTargetQuery(.{
            .cpu_arch = .wasm32,
            .os_tag = .freestanding,
        }),
        .optimize = .ReleaseSafe,
    });
    burble_fft.entry = .disabled;
    for (fft_exports) |exp| burble_fft.rdynamic = true;
    _ = fft_exports;
    b.installArtifact(burble_fft);
}
