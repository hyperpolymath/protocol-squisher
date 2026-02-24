// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <jonathan.jewell@open.ac.uk>
//
// Protocol Squisher FFI Implementation
//
// Provides C-compatible FFI functions for protocol compatibility analysis
// and adapter generation. Types match the Idris2 ABI definitions in src/abi/.

const std = @import("std");

/// Supported protocol formats matching Idris2 ProtocolFormat
pub const ProtocolFormat = enum(u8) {
    protobuf = 0,
    avro = 1,
    thrift = 2,
    capnproto = 3,
    bebop = 4,
    flatbuffers = 5,
    messagepack = 6,
    json_schema = 7,
    rescript = 8,
    python = 9,
};

/// Transport class matching Idris2 TransportClass
pub const TransportClass = enum(u8) {
    concorde = 0, // Zero-copy, 100% fidelity
    business = 1, // Minor overhead, 98% fidelity
    economy = 2, // Moderate overhead, 80% fidelity
    wheelbarrow = 3, // High overhead, 50% fidelity (JSON fallback)
};

/// Compatibility result matching Idris2 CompatResultFFI
pub const CompatResultFFI = extern struct {
    source_format: u8,
    target_format: u8,
    transport_class: u8,
    fidelity: u32, // percentage * 100
};

/// Field mapping matching Idris2 FieldMappingFFI
pub const FieldMappingFFI = extern struct {
    source_field_idx: u32,
    target_field_idx: u32,
    transport_class: u8,
    fidelity: u32,
};

/// Adapter result matching Idris2 AdapterFFI
pub const AdapterFFI = extern struct {
    source_format: u8,
    target_format: u8,
    mapping_count: u32,
    overall_class: u8,
};

/// C callback function type for bridge events
pub const SquisherCallback = ?*const fn (event_code: i32, value: i32, ctx: ?*anyopaque) callconv(.c) void;

/// Internal handle state
const HandleData = struct {
    mappings: std.ArrayList(FieldMappingFFI),
    last_adapter: ?AdapterFFI,
    owned_buffers: std.ArrayList([]u8),
    callback: SquisherCallback,
    callback_ctx: ?*anyopaque,
    allocator: std.mem.Allocator,
};

var handles: std.AutoHashMap(i32, *HandleData) = undefined;
var next_handle: i32 = 1;
var initialized: bool = false;

/// Initialize the protocol squisher engine.
/// Returns a handle (>0) on success, -1 on failure.
export fn squisher_init() callconv(.c) i32 {
    if (!initialized) {
        handles = std.AutoHashMap(i32, *HandleData).init(std.heap.page_allocator);
        initialized = true;
    }
    const handle = next_handle;
    next_handle += 1;
    const data = std.heap.page_allocator.create(HandleData) catch return -1;
    data.* = HandleData{
        .mappings = .{},
        .last_adapter = null,
        .owned_buffers = .{},
        .callback = null,
        .callback_ctx = null,
        .allocator = std.heap.page_allocator,
    };
    handles.put(handle, data) catch return -1;
    return handle;
}

/// Free resources associated with a squisher handle.
export fn squisher_free(handle: i32) callconv(.c) void {
    if (handles.fetchRemove(handle)) |kv| {
        for (kv.value.owned_buffers.items) |buf| {
            kv.value.allocator.free(buf);
        }
        kv.value.owned_buffers.deinit(kv.value.allocator);
        kv.value.mappings.deinit(kv.value.allocator);
        std.heap.page_allocator.destroy(kv.value);
    }
}

/// Generic function-call bridge operation.
/// op_code: 0=add, 1=sub, 2=mul, 3=div
export fn squisher_bridge_call(handle: i32, op_code: i32, lhs: i32, rhs: i32) callconv(.c) i32 {
    const data = handles.get(handle) orelse return -1;
    const result = switch (op_code) {
        0 => lhs + rhs,
        1 => lhs - rhs,
        2 => lhs * rhs,
        3 => if (rhs == 0) return -1 else @divTrunc(lhs, rhs),
        else => return -1,
    };

    if (data.callback) |cb| {
        cb(1, result, data.callback_ctx);
    }
    return result;
}

/// Allocate a handle-owned buffer and return pointer.
/// Buffer lifetime is tied to handle or explicit `squisher_free_buffer`.
export fn squisher_alloc_buffer(handle: i32, size: u32) callconv(.c) ?[*]u8 {
    const data = handles.get(handle) orelse return null;
    if (size == 0) return null;

    const slice = data.allocator.alloc(u8, size) catch return null;
    data.owned_buffers.append(data.allocator, slice) catch {
        data.allocator.free(slice);
        return null;
    };
    return slice.ptr;
}

/// Free a previously allocated handle-owned buffer.
export fn squisher_free_buffer(handle: i32, ptr: ?[*]u8) callconv(.c) i32 {
    const data = handles.get(handle) orelse return -1;
    if (ptr == null) return -1;
    const p = ptr.?;

    var i: usize = 0;
    while (i < data.owned_buffers.items.len) : (i += 1) {
        if (data.owned_buffers.items[i].ptr == p) {
            const buf = data.owned_buffers.swapRemove(i);
            data.allocator.free(buf);
            return 0;
        }
    }

    return -1;
}

/// Register callback for bridge events.
export fn squisher_register_callback(handle: i32, callback: SquisherCallback, ctx: ?*anyopaque) callconv(.c) i32 {
    const data = handles.get(handle) orelse return -1;
    data.callback = callback;
    data.callback_ctx = ctx;
    return 0;
}

/// Invoke currently registered callback manually.
export fn squisher_invoke_callback(handle: i32, event_code: i32, value: i32) callconv(.c) i32 {
    const data = handles.get(handle) orelse return -1;
    if (data.callback) |cb| {
        cb(event_code, value, data.callback_ctx);
        return 0;
    }
    return -1;
}

/// Measure average nanoseconds per bridged call.
export fn squisher_benchmark_bridge_calls(handle: i32, iterations: i32) callconv(.c) i64 {
    _ = handles.get(handle) orelse return -1;
    if (iterations <= 0) return -1;

    const start = std.time.nanoTimestamp();
    var i: i32 = 0;
    while (i < iterations) : (i += 1) {
        _ = squisher_bridge_call(handle, 0, i, 1);
    }
    const elapsed: i64 = @intCast(std.time.nanoTimestamp() - start);
    return @divTrunc(elapsed, @as(i64, iterations));
}

/// Measure average nanoseconds for a direct/manual call baseline.
export fn squisher_benchmark_direct_calls(iterations: i32) callconv(.c) i64 {
    if (iterations <= 0) return -1;

    const start = std.time.nanoTimestamp();
    var i: i32 = 0;
    while (i < iterations) : (i += 1) {
        _ = i + 1;
    }
    const elapsed: i64 = @intCast(std.time.nanoTimestamp() - start);
    return @divTrunc(elapsed, @as(i64, iterations));
}

/// Analyze compatibility between two protocol formats.
/// Returns TransportClass enum value (0-3), or -1 on error.
export fn squisher_analyze_compatibility(handle: i32, source_format: i32, target_format: i32) callconv(.c) i32 {
    _ = handles.get(handle) orelse return -1;

    // Validate format values
    if (source_format < 0 or source_format > 9) return -1;
    if (target_format < 0 or target_format > 9) return -1;

    // Same format is always Concorde (zero-copy)
    if (source_format == target_format) {
        return @intFromEnum(TransportClass.concorde);
    }

    // Cross-format analysis based on protocol characteristics
    const src: u8 = @intCast(source_format);
    const tgt: u8 = @intCast(target_format);
    const class = analyze_format_pair(src, tgt);
    return @intFromEnum(class);
}

/// Determine transport class for a protocol format pair.
/// Schema-based strongly-typed formats get better classes
/// than schema-less formats like MessagePack.
fn analyze_format_pair(source: u8, target: u8) TransportClass {
    const src = std.meta.intToEnum(ProtocolFormat, source) catch return TransportClass.wheelbarrow;
    const tgt = std.meta.intToEnum(ProtocolFormat, target) catch return TransportClass.wheelbarrow;

    // MessagePack is schema-less: always Wheelbarrow when crossing formats
    if (src == .messagepack or tgt == .messagepack) {
        return TransportClass.wheelbarrow;
    }

    // Binary schema-based protocols can often achieve Business class
    const src_binary = is_binary_schema(src);
    const tgt_binary = is_binary_schema(tgt);

    if (src_binary and tgt_binary) {
        return TransportClass.business;
    }

    // Text/IDL based cross-conversions typically Economy
    return TransportClass.economy;
}

/// Check if a protocol format uses binary schema encoding
fn is_binary_schema(fmt: ProtocolFormat) bool {
    return switch (fmt) {
        .protobuf, .avro, .thrift, .capnproto, .flatbuffers, .bebop => true,
        .messagepack, .json_schema, .rescript, .python => false,
    };
}

/// Generate an adapter between two protocol schemas.
/// Current implementation stores transport metadata and leaves field mappings empty.
export fn squisher_generate_adapter(
    handle: i32,
    _source_schema: [*:0]const u8,
    _target_schema: [*:0]const u8,
    source_format: i32,
    target_format: i32,
) callconv(.c) i32 {
    const data = handles.get(handle) orelse return -1;
    _ = _source_schema;
    _ = _target_schema;

    if (source_format < 0 or source_format > 9) return -1;
    if (target_format < 0 or target_format > 9) return -1;

    // Clear previous mappings
    data.mappings.clearRetainingCapacity();

    // Store adapter metadata
    const src_u8: u8 = @intCast(source_format);
    const tgt_u8: u8 = @intCast(target_format);
    const class = analyze_format_pair(src_u8, tgt_u8);

    data.last_adapter = AdapterFFI{
        .source_format = src_u8,
        .target_format = tgt_u8,
        .mapping_count = 0,
        .overall_class = @intFromEnum(class),
    };

    if (data.callback) |cb| {
        cb(2, @intCast(@intFromEnum(class)), data.callback_ctx);
    }

    return 0;
}

/// Get the number of field mappings in the last generated adapter.
export fn squisher_get_mapping_count(handle: i32) callconv(.c) i32 {
    const data = handles.get(handle) orelse return -1;
    return @intCast(data.mappings.items.len);
}

/// Get the overall transport class for the last generated adapter.
export fn squisher_get_transport_class(handle: i32) callconv(.c) i32 {
    const data = handles.get(handle) orelse return -1;
    if (data.last_adapter) |adapter| {
        return @intCast(adapter.overall_class);
    }
    return -1;
}

/// Get the number of supported protocol formats. Always returns 10.
export fn squisher_format_count() callconv(.c) i32 {
    return 10;
}

// Tests
test "protocol format values" {
    try std.testing.expectEqual(@as(u8, 0), @intFromEnum(ProtocolFormat.protobuf));
    try std.testing.expectEqual(@as(u8, 9), @intFromEnum(ProtocolFormat.python));
}

test "transport class values" {
    try std.testing.expectEqual(@as(u8, 0), @intFromEnum(TransportClass.concorde));
    try std.testing.expectEqual(@as(u8, 3), @intFromEnum(TransportClass.wheelbarrow));
}

test "compat result struct size" {
    try std.testing.expectEqual(@as(usize, 8), @sizeOf(CompatResultFFI));
}

test "field mapping struct size" {
    try std.testing.expectEqual(@as(usize, 16), @sizeOf(FieldMappingFFI));
}

test "init and free" {
    const h = squisher_init();
    try std.testing.expect(h > 0);
    squisher_free(h);
}

test "format count" {
    try std.testing.expectEqual(@as(i32, 10), squisher_format_count());
}

test "same format compatibility is concorde" {
    const h = squisher_init();
    defer squisher_free(h);

    const result = squisher_analyze_compatibility(h, 0, 0); // protobuf to protobuf
    try std.testing.expectEqual(@as(i32, 0), result); // Concorde
}

test "cross format binary compatibility is business" {
    const h = squisher_init();
    defer squisher_free(h);

    const result = squisher_analyze_compatibility(h, 0, 1); // protobuf to avro
    try std.testing.expectEqual(@as(i32, 1), result); // Business
}

test "messagepack always wheelbarrow" {
    const h = squisher_init();
    defer squisher_free(h);

    const result = squisher_analyze_compatibility(h, 6, 0); // messagepack to protobuf
    try std.testing.expectEqual(@as(i32, 3), result); // Wheelbarrow
}

test "invalid format returns error" {
    const h = squisher_init();
    defer squisher_free(h);

    const result = squisher_analyze_compatibility(h, -1, 0);
    try std.testing.expectEqual(@as(i32, -1), result);
}

test "bridge call arithmetic" {
    const h = squisher_init();
    defer squisher_free(h);

    try std.testing.expectEqual(@as(i32, 7), squisher_bridge_call(h, 0, 3, 4));
    try std.testing.expectEqual(@as(i32, 2), squisher_bridge_call(h, 1, 6, 4));
    try std.testing.expectEqual(@as(i32, 15), squisher_bridge_call(h, 2, 3, 5));
}

test "owned buffer allocation and free" {
    const h = squisher_init();
    defer squisher_free(h);

    const ptr = squisher_alloc_buffer(h, 32) orelse return error.TestExpectedNonNull;
    ptr[0] = 0xAA;
    try std.testing.expectEqual(@as(i32, 0), squisher_free_buffer(h, ptr));
}

test "callback registration and invoke" {
    const Ctx = struct {
        var called: bool = false;
    };

    const Callbacks = struct {
        fn on_event(_event: i32, _value: i32, _ctx: ?*anyopaque) callconv(.c) void {
            _ = _event;
            _ = _value;
            _ = _ctx;
            Ctx.called = true;
        }
    };

    const h = squisher_init();
    defer squisher_free(h);

    try std.testing.expectEqual(
        @as(i32, 0),
        squisher_register_callback(h, Callbacks.on_event, null),
    );
    try std.testing.expectEqual(@as(i32, 0), squisher_invoke_callback(h, 99, 42));
    try std.testing.expect(Ctx.called);
}

test "bridge benchmark returns positive ns" {
    const h = squisher_init();
    defer squisher_free(h);

    const avg_ns = squisher_benchmark_bridge_calls(h, 1_000);
    const direct_ns = squisher_benchmark_direct_calls(1_000);
    try std.testing.expect(avg_ns > 0);
    try std.testing.expect(direct_ns > 0);
    // Keep bridge overhead in a practical bound for FFI replacement viability.
    try std.testing.expect(avg_ns <= direct_ns * 5000);
}

test "invalid handle returns error" {
    const result = squisher_analyze_compatibility(999, 0, 0);
    try std.testing.expectEqual(@as(i32, -1), result);
}
