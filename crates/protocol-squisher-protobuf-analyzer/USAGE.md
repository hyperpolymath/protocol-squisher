# Protobuf Analyzer Usage Guide

Complete guide to using the protocol-squisher Protobuf analyzer.

## Installation

Add to your `Cargo.toml`:

```toml
[dependencies]
protocol-squisher-protobuf-analyzer = { path = "../protocol-squisher-protobuf-analyzer" }
protocol-squisher-ir = { path = "../protocol-squisher-ir" }
protocol-squisher-transport-primitives = { path = "../../ephapax-ir" }
```

## Basic Usage

### Analyze a .proto file

```rust
use protocol_squisher_protobuf_analyzer::ProtobufAnalyzer;
use std::path::Path;

let analyzer = ProtobufAnalyzer::new();
let schema = analyzer.analyze_file(Path::new("schema.proto"))?;

// Access types
for (name, type_def) in &schema.types {
    println!("Found type: {}", name);
}
```

### Analyze from a string

```rust
let proto = r#"
    syntax = "proto3";

    message User {
        int32 id = 1;
        string name = 2;
    }
"#;

let analyzer = ProtobufAnalyzer::new();
let schema = analyzer.analyze_str(proto, "user")?;
```

## Working with Types

### Structs (Messages)

```rust
use protocol_squisher_ir::TypeDef;

if let Some(TypeDef::Struct(user_struct)) = schema.types.get("User") {
    println!("Struct: {}", user_struct.name);

    for field in &user_struct.fields {
        println!("  Field: {} : {:?}", field.name, field.ty);

        if field.optional {
            println!("    (optional)");
        }
    }
}
```

### Enums

```rust
if let Some(TypeDef::Enum(status_enum)) = schema.types.get("Status") {
    println!("Enum: {}", status_enum.name);

    for variant in &status_enum.variants {
        println!("  Variant: {}", variant.name);

        if let Some(payload) = &variant.payload {
            println!("    Payload: {:?}", payload);
        }
    }
}
```

## Transport Class Analysis

### Check compatibility between types

```rust
use protocol_squisher_protobuf_analyzer::TransportAnalysis;
use protocol_squisher_transport_primitives::IRContext;

let ctx = IRContext::new();

// Get types from schema
let source_type = /* ... */;
let target_type = /* ... */;

// Analyze compatibility
let analysis = TransportAnalysis::new(&ctx, source_type, target_type)?;

match analysis.class {
    TransportClass::Concorde => {
        println!("Perfect match - zero-copy!");
        assert_eq!(analysis.fidelity, 100);
        assert_eq!(analysis.overhead, 0);
    }
    TransportClass::Business => {
        println!("Safe widening - minor overhead");
        assert_eq!(analysis.fidelity, 98);
        assert_eq!(analysis.overhead, 5);
    }
    TransportClass::Economy => {
        println!("Lossy conversion");
    }
    TransportClass::Wheelbarrow => {
        println!("Incompatible - requires JSON");
        assert_eq!(analysis.fidelity, 50);
        assert_eq!(analysis.overhead, 80);
    }
}
```

### Convenience methods

```rust
if analysis.is_zero_copy() {
    // Can use memcpy
}

if analysis.is_safe() {
    // No data loss
}

if analysis.requires_json_fallback() {
    // Must serialize through JSON
}
```

## Advanced Features

### Handling Nested Types

Nested messages are automatically flattened with underscore naming:

```protobuf
message Outer {
    message Inner {
        string value = 1;
    }
}
```

Becomes:
- `Outer` struct
- `Outer_Inner` struct

Access nested types:

```rust
let outer = schema.types.get("Outer").unwrap();
let inner = schema.types.get("Outer_Inner").unwrap();
```

### Working with Oneofs

Oneofs are converted to enum types with variant payloads:

```protobuf
message Payment {
    oneof method {
        string card_number = 1;
        string bank_account = 2;
    }
}
```

Becomes:
- `Payment` struct with `method: Option<Payment_Method>` field
- `Payment_Method` enum with `CardNumber(String)` and `BankAccount(String)` variants

```rust
if let Some(TypeDef::Enum(method_enum)) = schema.types.get("Payment_Method") {
    for variant in &method_enum.variants {
        if let Some(VariantPayload::Tuple(fields)) = &variant.payload {
            println!("{} contains: {:?}", variant.name, fields);
        }
    }
}
```

### Maps

Maps are represented as `Map<K, V>` containers:

```protobuf
message Config {
    map<string, int32> counters = 1;
}
```

```rust
use protocol_squisher_ir::{IrType, ContainerType};

if let Some(TypeDef::Struct(config)) = schema.types.get("Config") {
    let counters_field = &config.fields[0];

    if let IrType::Container(ContainerType::Map(key_type, value_type)) = &counters_field.ty {
        println!("Map from {:?} to {:?}", key_type, value_type);
    }
}
```

### Repeated Fields

Repeated fields become `Vec<T>`:

```protobuf
message User {
    repeated string tags = 1;
}
```

```rust
if let IrType::Container(ContainerType::Vec(element_type)) = &field.ty {
    println!("Array of {:?}", element_type);
}
```

## Type Mappings Reference

### Scalar Types

| Protobuf | IR Type | Rust Equivalent |
|----------|---------|-----------------|
| `double` | `F64` | `f64` |
| `float` | `F32` | `f32` |
| `int32` | `I32` | `i32` |
| `int64` | `I64` | `i64` |
| `uint32` | `U32` | `u32` |
| `uint64` | `U64` | `u64` |
| `sint32` | `I32` | `i32` |
| `sint64` | `I64` | `i64` |
| `fixed32` | `U32` | `u32` |
| `fixed64` | `U64` | `u64` |
| `sfixed32` | `I32` | `i32` |
| `sfixed64` | `I64` | `i64` |
| `bool` | `Bool` | `bool` |
| `string` | `String` | `String` |
| `bytes` | `Bytes` | `Vec<u8>` |

### Container Types

| Protobuf | IR Type |
|----------|---------|
| `repeated T` | `Vec<T>` |
| `map<K, V>` | `Map<K, V>` |
| `optional T` (proto3) | `Option<T>` |

### Complex Types

| Protobuf | IR Type |
|----------|---------|
| `message` | `Struct` |
| `enum` | `Enum` |
| `oneof` | `Enum` with variant payloads |

## Error Handling

```rust
use protocol_squisher_protobuf_analyzer::AnalyzerError;

match analyzer.analyze_file(path) {
    Ok(schema) => { /* success */ }
    Err(AnalyzerError::ParseError(msg)) => {
        eprintln!("Failed to parse proto: {}", msg);
    }
    Err(AnalyzerError::InvalidProto(msg)) => {
        eprintln!("Invalid protobuf: {}", msg);
    }
    Err(AnalyzerError::UnsupportedFeature(msg)) => {
        eprintln!("Unsupported: {}", msg);
    }
    Err(AnalyzerError::Io(err)) => {
        eprintln!("IO error: {}", err);
    }
}
```

## Examples

See the `examples/` directory for complete working examples:

- `analyze_proto.rs` - Basic schema analysis and introspection
- `transport_analysis.rs` - Field-by-field transport compatibility
- `complex_schema.rs` - Complex nested schema with oneofs and maps

Run examples with:

```bash
cargo run --example analyze_proto
cargo run --example transport_analysis
cargo run --example complex_schema
```

## Testing

Run the comprehensive test suite:

```bash
cargo test -p protocol-squisher-protobuf-analyzer
```

Test coverage includes:
- Proto2 and proto3 syntax
- All scalar types
- Messages (flat and nested)
- Enums (top-level and nested)
- Repeated fields
- Map fields
- Oneof groups
- Comments (single-line and multi-line)
- Package declarations
- Transport class analysis

## Limitations

### Currently Not Supported

- **Services/RPCs**: Only message and enum types
- **Custom options**: Ignored during parsing
- **Extensions**: Not parsed
- **Groups**: Deprecated syntax not supported
- **Imports**: Not resolved (each file analyzed independently)
- **Reserved fields**: Skipped during parsing

### Future Enhancements

See README.md for planned features and roadmap.

## Performance

The analyzer uses regex-based parsing optimized for:
- **Speed**: Fast parsing of typical .proto files (< 1ms for small schemas)
- **Memory**: Minimal allocations with string interning
- **Correctness**: Careful handling of nested braces and comments

For very large schemas (> 1000 types), consider analyzing incrementally by package.

## Contributing

Contributions welcome! Key areas:

1. **Service definitions**: Extract RPC methods and types
2. **Import resolution**: Follow and analyze dependencies
3. **Better errors**: Line numbers and detailed messages
4. **Validation**: Enforce protobuf rules (e.g., enum 0 value)

## License

PMPL-1.0-or-later
