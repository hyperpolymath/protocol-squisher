// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <jonathan.jewell@open.ac.uk>
//
// Integration tests for protocol-squisher FFI

const std = @import("std");
const main = @import("../src/main.zig");

test "full lifecycle: init, analyze, free" {
    const handle = main.squisher_init();
    try std.testing.expect(handle > 0);

    // Analyze protobuf to avro compatibility
    const result = main.squisher_analyze_compatibility(handle, 0, 1);
    try std.testing.expect(result >= 0);
    try std.testing.expect(result <= 3);

    main.squisher_free(handle);
}

test "multiple handles are independent" {
    const h1 = main.squisher_init();
    const h2 = main.squisher_init();

    try std.testing.expect(h1 != h2);
    try std.testing.expect(h1 > 0);
    try std.testing.expect(h2 > 0);

    main.squisher_free(h1);
    main.squisher_free(h2);
}

test "all protocol format pairs produce valid results" {
    const handle = main.squisher_init();
    defer main.squisher_free(handle);

    var src: i32 = 0;
    while (src < 10) : (src += 1) {
        var tgt: i32 = 0;
        while (tgt < 10) : (tgt += 1) {
            const result = main.squisher_analyze_compatibility(handle, src, tgt);
            try std.testing.expect(result >= 0);
            try std.testing.expect(result <= 3);

            // Same format should always be Concorde
            if (src == tgt) {
                try std.testing.expectEqual(@as(i32, 0), result);
            }
        }
    }
}

test "format count is always 10" {
    try std.testing.expectEqual(@as(i32, 10), main.squisher_format_count());
}
