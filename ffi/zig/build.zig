// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// Build configuration for protocol-squisher FFI library.
//
// PURPOSE: Provides C-compatible FFI functions for protocol compatibility
// analysis and adapter generation. Types match the Idris2 ABI definitions
// in src/abi/. Performance-critical paths (format pair analysis, bridge
// arithmetic, buffer management) are implemented in Zig for zero-overhead
// C ABI compatibility and cross-compilation.
//
// PRODUCES:
//   zig-out/lib/libprotocol_squisher_ffi.so  (shared library)
//   zig-out/lib/libprotocol_squisher_ffi.a   (static library)
//
// BUILD:  zig build
// TEST:   zig build test

const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // Create the root module for the FFI source
    const root_module = b.createModule(.{
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });

    // Build shared library
    const shared_lib = b.addLibrary(.{
        .linkage = .dynamic,
        .name = "protocol_squisher_ffi",
        .root_module = root_module,
    });
    b.installArtifact(shared_lib);

    // Build static library
    const static_lib = b.addLibrary(.{
        .linkage = .static,
        .name = "protocol_squisher_ffi",
        .root_module = root_module,
    });
    b.installArtifact(static_lib);

    // Unit tests
    const unit_tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });

    const run_unit_tests = b.addRunArtifact(unit_tests);

    const test_step = b.step("test", "Run unit tests");
    test_step.dependOn(&run_unit_tests.step);
}
