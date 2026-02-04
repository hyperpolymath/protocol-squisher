# Protocol Analyzers in Ephapax

This directory contains protocol analyzers written in the ephapax language. These analyzers demonstrate ephapax's capability for protocol analysis and type-safe schema processing.

## Implemented Analyzers

All 7 protocol analyzers are implemented:

| Protocol | File | Description | Output |
|----------|------|-------------|--------|
| **Bebop** | `bebop-simple.eph` | Modern schema-based format with zero-copy design | 60 |
| **FlatBuffers** | `flatbuffers-simple.eph` | Google's zero-copy serialization with vtables | 30 |
| **MessagePack** | `messagepack-simple.eph` | Compact binary serialization (no zero-copy) | 148 |
| **Avro** | `avro-simple.eph` | Apache schema-based format with compact encoding | 113 |
| **Cap'n Proto** | `capnproto-simple.eph` | Zero-copy with pointer-based access | 8 |
| **Thrift** | `thrift-simple.eph` | Apache RPC framework with compact protocol | 78 |
| **Protocol Buffers** | `protobuf-simple.eph` | Google's wire format with varint encoding | 95 |

## Running the Analyzers

From the `compiler` directory:

```bash
# Run individual analyzer
cargo run --release -- ../analyzers/bebop-simple.eph

# Run all analyzers
./run-all-analyzers.sh
```

## Output Interpretation

The output number represents the total overhead score for the analyzed schema:

- **Lower scores** = more efficient (zero-copy or minimal overhead)
- **Higher scores** = more overhead (serialization required)

Examples:
- Cap'n Proto (8) - highly optimized for zero-copy
- FlatBuffers (30) - zero-copy for primitives
- Bebop (60) - moderate overhead from string field
- Protobuf (95) - wire format encoding overhead
- Avro (113) - variable-length encoding overhead
- MessagePack (148) - full serialization required

## Analyzer Components

Each analyzer implements:

1. **Type Constants** - Protocol-specific type identifiers
2. **IR Mapping** - Conversion to intermediate representation
3. **Overhead Calculation** - Analysis of serialization/memory costs
4. **Transport Class** - Zero-copy vs serialization classification
5. **Schema Analysis** - Example schema with multiple fields

## Ephapax Language Features Used

- ✅ Functions with parameters and return types
- ✅ Integer and boolean primitives
- ✅ String type and concatenation
- ✅ Pattern matching (match expressions)
- ✅ Linear types (resource safety)
- ✅ Copy trait (primitives can be reused)

## Future Enhancements

To write more sophisticated analyzers, ephapax will need:

- [ ] **Arrays/Vectors** - For handling lists of fields
- [ ] **Structs/Records** - For representing schemas
- [ ] **Enums** - For representing type variants
- [ ] **File I/O** - For parsing schema files
- [ ] **HashMap** - For name-to-type mappings
- [ ] **Result/Option types** - For error handling

## Example: Bebop Analyzer

```ephapax
// Define type constants
fn bebop_int32() -> i32 { 1 }
fn bebop_string() -> i32 { 8 }

// Calculate overhead
fn is_zero_copy(bebop_type: i32) -> bool {
    match bebop_type {
        1 => true,   // int32 is zero-copy
        8 => false,  // string requires indirection
        _ => false
    }
}

// Analyze schema
fn analyze_schema() -> i32 {
    let field1_score = analyze_field(bebop_int32(), ir_i32());
    let field2_score = analyze_field(bebop_string(), ir_string());
    field1_score + field2_score
}
```

## Integration with Protocol-Squisher

These analyzers demonstrate the foundation for ephapax-based protocol analysis. The full integration would:

1. Parse schema files (`.bop`, `.fbs`, `.proto`, etc.)
2. Build type mappings and field lists
3. Analyze compatibility between protocols
4. Generate optimal conversion strategies
5. Compile to WASM for browser/embedded use

## Performance

Current interpreter performance is suitable for development and testing. For production:

- Use `--wasm` flag to compile to WebAssembly
- WASM compilation enables near-native performance
- Zero-copy analysis can be performed at compile-time

## See Also

- [../WASM-BACKEND-COMPLETE.md](../WASM-BACKEND-COMPLETE.md) - WASM compilation
- [../OPERATORS-AND-BORROWING-COMPLETE.md](../OPERATORS-AND-BORROWING-COMPLETE.md) - Language features
- [../compiler/README.md](../compiler/README.md) - Compiler documentation
