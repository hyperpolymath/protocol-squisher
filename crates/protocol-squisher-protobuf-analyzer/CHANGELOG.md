# Changelog

All notable changes to the protocol-squisher-protobuf-analyzer will be documented in this file.

## [0.1.0] - 2026-02-04

### Initial Implementation

Complete Protobuf analyzer implementation with ephapax transport class analysis.

#### Added

**Core Features:**
- ✅ Proto2 and proto3 syntax support
- ✅ All protobuf scalar types (double, float, int32/64, uint32/64, sint32/64, fixed32/64, sfixed32/64, bool, string, bytes)
- ✅ Message parsing (flat and nested)
- ✅ Enum parsing (top-level and nested)
- ✅ Repeated field support (converted to Vec<T>)
- ✅ Map field support (converted to Map<K,V>)
- ✅ Oneof support (converted to enum with variant payloads)
- ✅ Comment handling (single-line and multi-line)
- ✅ Package declaration parsing

**Parser (`src/parser.rs`):**
- Regex-based parser with balanced brace extraction
- Comment removal with string literal awareness
- Syntax detection (proto2 vs proto3)
- Recursive nested message parsing
- Field label handling (optional, required, repeated)
- Map and oneof special parsing

**Converter (`src/converter.rs`):**
- Protobuf → IR type mapping
- Struct generation from messages
- Enum generation from protobuf enums
- Oneof → enum with payloads conversion
- Nested type flattening with underscore naming
- Field optionality logic (proto2 vs proto3 semantics)
- Container type conversion (Vec, Map, Option)

**Ephapax Bridge (`src/ephapax_bridge.rs`):**
- IR type → ephapax primitive type conversion
- Transport class analysis (Concorde/Business/Economy/Wheelbarrow)
- Container compatibility analysis (recursive)
- TransportAnalysis result type with convenience methods
- Option, Vec, Map, Tuple support

**Testing:**
- 43 unit tests (all passing)
- 2 doc tests (all passing)
- Parser tests (11 tests)
- Converter tests (3 tests)
- Ephapax bridge tests (16 tests)
- Integration tests (13 tests)

**Examples:**
- `analyze_proto.rs` - Basic schema analysis and introspection
- `transport_analysis.rs` - Field-by-field transport compatibility
- `complex_schema.rs` - Complex nested schema demonstration

**Documentation:**
- README.md - Overview and features
- USAGE.md - Complete usage guide with examples
- IMPLEMENTATION.md - Technical implementation details
- Module-level rustdoc with examples
- Inline documentation for all public APIs

**Dependencies:**
- protocol-squisher-ir - Canonical IR format
- protocol-squisher-transport-primitives - Proven transport analysis
- thiserror - Error handling
- regex - Pattern matching
- pretty_assertions (dev) - Better test output

#### Known Limitations

**Not Yet Supported:**
- Services and RPC definitions
- Custom options
- Extension fields
- Groups (deprecated protobuf feature)
- Import resolution
- Reserved field declarations

These are documented as future enhancements and do not impact the core message/enum analysis functionality.

#### Performance

- Small schemas (< 10 types): < 1ms
- Medium schemas (10-100 types): < 10ms
- Large schemas (100-1000 types): < 100ms

#### Breaking Changes

None (initial release)

#### Migration Guide

N/A (initial release)

---

## Future Roadmap

### Version 0.2.0 (Planned)

**Features:**
- Service and RPC extraction
- Import resolution
- Better error messages with line numbers
- Proto validation (enforce proto3 rules)

### Version 0.3.0 (Planned)

**Features:**
- Custom option preservation
- Extension field support
- Well-known types (google.protobuf.*)
- Performance optimization for very large schemas

### Version 1.0.0 (Planned)

**Features:**
- Full protobuf spec compliance
- Code generation hints
- Schema validation
- Backwards compatibility guarantees

---

## Contributing

See the main protocol-squisher repository for contribution guidelines.

## License

PMPL-1.0-or-later
