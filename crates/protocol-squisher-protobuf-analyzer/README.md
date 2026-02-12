# Protocol Squisher Protobuf Analyzer

Analyzes Protocol Buffer (.proto) schema files and converts them to the protocol-squisher canonical IR format with ephapax transport class analysis.

## Features

### Supported Protobuf Features

- **Both proto2 and proto3 syntax**
- **Messages**: Flat and nested messages
- **Fields**: All standard field types (scalar, message references, enums)
- **Field Labels**: `optional`, `required` (proto2), `repeated`
- **Enums**: Top-level and nested enums
- **Oneofs**: Union types with multiple alternatives
- **Maps**: Key-value map fields (`map<K, V>`)
- **Comments**: Single-line (`//`) and multi-line (`/* */`)
- **Packages**: Package declarations

### Protobuf Type Mappings

| Protobuf Type | IR Type | Ephapax Primitive |
|--------------|---------|-------------------|
| `double` | `F64` | `F64` |
| `float` | `F32` | `F32` |
| `int32`, `sint32`, `sfixed32` | `I32` | `I32` |
| `int64`, `sint64`, `sfixed64` | `I64` | `I64` |
| `uint32`, `fixed32` | `U32` | `U32` |
| `uint64`, `fixed64` | `U64` | `U64` |
| `bool` | `Bool` | `Bool` |
| `string` | `String` | `String` |
| `bytes` | `Bytes` | N/A (Vec<U8>) |
| `repeated T` | `Vec<T>` | Container |
| `map<K, V>` | `Map<K, V>` | Container |
| `oneof` | Enum with variants | Complex |

## Usage

### Basic Example

```rust
use protocol_squisher_protobuf_analyzer::ProtobufAnalyzer;
use std::path::Path;

let analyzer = ProtobufAnalyzer::new();

// Analyze from file
let schema = analyzer.analyze_file(Path::new("schema.proto"))?;

// Analyze from string
let proto = r#"
    syntax = "proto3";

    message User {
        string name = 1;
        int32 age = 2;
        repeated string tags = 3;
    }
"#;

let schema = analyzer.analyze_str(proto, "user")?;
```

### Transport Class Analysis

Use the ephapax bridge to analyze transport compatibility between protobuf types:

```rust
use protocol_squisher_protobuf_analyzer::{ProtobufAnalyzer, TransportAnalysis};
use protocol_squisher_transport_primitives::IRContext;

let analyzer = ProtobufAnalyzer::new();
let schema = analyzer.analyze_str(proto_content, "schema")?;

// Get types from the schema
let source_type = &schema.types.get("SourceMessage").unwrap();
let target_type = &schema.types.get("TargetMessage").unwrap();

// Analyze transport compatibility
let ctx = IRContext::new();
let analysis = TransportAnalysis::new(&ctx, source_type, target_type)?;

println!("Transport class: {:?}", analysis.class);
println!("Fidelity: {}%", analysis.fidelity);
println!("Overhead: {}%", analysis.overhead);

if analysis.is_zero_copy() {
    println!("Zero-copy transport available!");
} else if analysis.requires_json_fallback() {
    println!("JSON fallback required");
}
```

## Advanced Features

### Nested Messages

Nested messages are flattened with underscore naming:

```protobuf
message Outer {
    message Inner {
        string value = 1;
    }
    Inner inner = 1;
}
```

Becomes:
- `Outer` struct
- `Outer_Inner` struct

### Oneof Fields

Oneof groups are converted to enum types:

```protobuf
message Payment {
    oneof method {
        string card_number = 1;
        string bank_account = 2;
    }
}
```

Becomes:
- `Payment` struct with optional `Payment_Method` field
- `Payment_Method` enum with `CardNumber(String)` and `BankAccount(String)` variants

### Map Fields

Maps are represented as `Map<K, V>` container types:

```protobuf
message Config {
    map<string, string> settings = 1;
}
```

Becomes:
- `Config` struct with `settings: Map<String, String>` field

## Implementation Details

### Parser Architecture

The parser uses a regex-based approach with careful handling of:
- **Balanced braces**: Correctly extracts nested message/enum bodies
- **Comment removal**: Strips single-line and multi-line comments
- **Syntax detection**: Determines proto2 vs proto3
- **Nested structures**: Recursively parses nested messages and enums

### Converter Logic

1. **Type mapping**: Converts protobuf primitives to IR primitives
2. **Container handling**: Wraps repeated fields in `Vec<T>`, maps in `Map<K, V>`
3. **Optional fields**: Wraps in `Option<T>` based on syntax and label
4. **Naming**: Flattens nested types with underscore prefixes
5. **Enums**: Converts both regular enums and oneofs

### Ephapax Integration

The ephapax bridge provides:
- **Primitive mapping**: IR types → ephapax primitive types
- **Container analysis**: Recursive compatibility analysis for Vec, Map, Option, Tuple
- **Transport classification**: Concorde (zero-copy), Business (safe widening), Economy (lossy), Wheelbarrow (incompatible)

## Testing

Run the test suite:

```bash
cargo test -p protocol-squisher-protobuf-analyzer
```

The test suite includes:
- 20+ unit tests covering all protobuf features
- Parser tests (syntax detection, comment removal, field parsing)
- Converter tests (type mapping, naming conventions)
- Integration tests (end-to-end analysis)
- Ephapax bridge tests (transport class analysis)

## Limitations

### Not Yet Supported

- **Services and RPCs**: Only message/enum types are analyzed
- **Options**: Custom options are ignored
- **Extensions**: Extension fields are not parsed
- **Groups**: Deprecated group syntax not supported
- **Reserved fields**: Reserved declarations are skipped
- **Imports**: Import statements are not resolved

### Future Work

- **Service definitions**: Analyze RPC methods and extract request/response types
- **Import resolution**: Follow import paths and analyze dependencies
- **Custom options**: Extract and preserve custom field/message options
- **Better error reporting**: More detailed parse error messages with line numbers
- **Proto validation**: Enforce protobuf rules (e.g., enum must have 0 value in proto3)

## License

PMPL-1.0-or-later

## See Also

- [protocol-squisher-ir](../protocol-squisher-ir) - Canonical IR format
- [protocol-squisher-transport-primitives](../../ephapax-ir) - Proven transport class analysis
- [protocol-squisher-rust-analyzer](../protocol-squisher-rust-analyzer) - Rust/serde analyzer
- [protocol-squisher-python-analyzer](../protocol-squisher-python-analyzer) - Python/Pydantic analyzer
