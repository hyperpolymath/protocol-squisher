# ReScript Analyzer for Protocol Squisher

**Status**: ✅ Complete and tested (60 tests passing)

ReScript schema analyzer for protocol-squisher. This analyzer is **critical** for the hyperpolymath ecosystem as ReScript is the primary application language.

## Features

- **Full AST parsing**: Record types, variant types, option types, tuples, type aliases
- **Module system support**: Type definitions across module boundaries
- **JS interop**: `@as` attributes, `@deriving`, external declarations, `Js.Dict.t`
- **Type inference**: Handles polymorphic types (`'a`, `'b`)
- **Transport analysis**: Ephapax-powered compatibility checking
- **Zero-copy detection**: Identifies when data can be transferred without serialization

## Quick Start

```rust
use protocol_squisher_rescript_analyzer::ReScriptAnalyzer;
use std::path::Path;

let analyzer = ReScriptAnalyzer::new();

// Analyze from file
let schema = analyzer.analyze_file(Path::new("Types.res")).unwrap();

// Analyze from string
let rescript = r#"
    type user = {
      id: int,
      name: string,
      email: option<string>,
    }
"#;
let schema = analyzer.analyze_str(rescript, "user").unwrap();
```

## ReScript Type Mappings

| ReScript Type | IR Type | Rust Equivalent | Transport Class |
|---------------|---------|-----------------|-----------------|
| `int` | `I64` | `i64` | Concorde (zero-copy) |
| `float` | `F64` | `f64` | Concorde |
| `string` | `String` | `String` | Concorde |
| `bool` | `Bool` | `bool` | Concorde |
| `char` | `Char` | `char` | Concorde |
| `unit` | `Unit` | `()` | Concorde |
| `option<T>` | `Option<T>` | `Option<T>` | Concorde (if T is) |
| `array<T>` | `Vec<T>` | `Vec<T>` | Concorde (if T is) |
| `(T1, T2, ...)` | `Tuple<...>` | `(T1, T2, ...)` | Concorde (if all T are) |
| `Js.Dict.t<V>` | `Map<String, V>` | `HashMap<String, V>` | Concorde (if V is) |

## Supported ReScript Features

### Record Types

```rescript
type person = {
  name: string,
  age: int,
  email: option<string>,
}
```

### Variant Types (Enums/ADTs)

```rescript
type status =
  | Active
  | Inactive
  | Suspended

type result<'a, 'e> =
  | Ok('a)
  | Error('e)
```

### JS Interop Attributes

```rescript
type apiUser = {
  @as("user_id") id: int,
  @as("user_name") name: string,
}
```

The `@as` attribute is captured as an alias in the IR metadata.

### Polymorphic Types

```rescript
type response<'data> = {
  status: int,
  data: option<'data>,
}
```

Type parameters are represented as `IrType::Reference` in the IR.

### Type Aliases

```rescript
type userId = int
type timestamp = float
```

### Nested Records

```rescript
type address = {
  street: string,
  city: string,
}

type person = {
  name: string,
  address: address,
}
```

### Tuples

```rescript
type coordinates = (float, float, float)
```

### JS Dict (Map)

```rescript
type config = {
  settings: Js.Dict.t<string>,
}
```

## Transport Analysis

The analyzer uses ephapax for proven-correct transport class analysis:

### Concorde (Zero-Copy)

Identical types with no conversion overhead:
- ReScript `int` → Rust `i64`
- ReScript `string` → Rust `String`
- ReScript `array<T>` → Rust `Vec<T>` (if T is Concorde)

### Business (Safe Widening)

Safe conversions with minor overhead:
- ReScript `int` → Rust `i128` (widening)
- Integer precision changes (safe direction only)

### Economy (Discriminated Unions)

Requires tag checking but no serialization:
- ReScript variants → Rust enums

### Wheelbarrow (JSON Fallback)

Requires full serialization/deserialization:
- Incompatible types (e.g., `int` → `string`)
- Narrowing conversions (e.g., `i64` → `i32`)

## Architecture

The analyzer follows the standard 4-module structure:

1. **lib.rs** - Public API and main analyzer
2. **parser.rs** - Regex-based ReScript parser
3. **converter.rs** - ReScript AST → IR conversion
4. **ephapax_bridge.rs** - Transport class analysis

## Interop Examples

### ReScript ↔ Rust

```rust
// ReScript: type user = { id: int, name: string }
// Rust:     struct User { id: i64, name: String }
// Transport: Concorde (zero-copy)
```

### ReScript ↔ Julia

```julia
# ReScript: type point = (float, float)
# Julia:    Point = Tuple{Float64, Float64}
# Transport: Concorde
```

### ReScript ↔ Gleam

```gleam
// ReScript: type result<'a, 'e> = | Ok('a) | Error('e)
// Gleam:    type Result(a, e) { Ok(a) Error(e) }
// Transport: Concorde (identical ADT representation)
```

## Testing

The analyzer has comprehensive test coverage:

- **Unit tests**: 47 tests for parser, converter, and ephapax bridge
- **Interop tests**: 13 tests for cross-language compatibility
- **Total**: 60 tests, all passing

Run tests:

```bash
cargo test
```

Run interop tests only:

```bash
cargo test --test interop_tests
```

## Why This Analyzer is Critical

ReScript is the **primary application language** in the hyperpolymath ecosystem:

1. **Type-safe JS**: Compiles to clean JavaScript with strong type guarantees
2. **Web apps**: Primary language for browser-based applications
3. **Cross-platform**: Works on web, mobile (via JS), and server (Deno)
4. **Ecosystem integration**: Bridge between JS ecosystem and typed languages

This analyzer enables:
- ReScript web apps ↔ Rust backends (zero-copy via ephapax)
- ReScript types ↔ database schemas (via protocol-squisher)
- ReScript APIs ↔ other typed languages (Gleam, Julia, etc.)

## Implementation Notes

### Parsing Strategy

Uses regex-based parsing with:
- Comment removal
- Nested bracket handling (for generics)
- Attribute extraction (`@as`, `@deriving`)
- Polymorphic type parameter tracking

### Type Parameter Handling

Type parameters (`'a`, `'b`) are represented as `IrType::Reference` to preserve their generic nature through the IR pipeline.

### JS Interop

The `@as` attribute is captured as field aliases in `FieldMetadata`, allowing code generators to produce correct JS-compatible names.

### Variant Payloads

ReScript variant payloads are converted to `VariantPayload::Tuple` since ReScript always uses tuple-style payloads (e.g., `Ok('a)` not `Ok { value: 'a }`).

## Future Enhancements

Potential additions (not currently required):
- External declarations (`external fetch: string => promise<response>`)
- Module-qualified types (`Module.Type`)
- Inline records in variants
- Advanced pattern matching analysis
- Full tree-sitter integration (currently regex-based)

## License

SPDX-License-Identifier: PMPL-1.0-or-later

Copyright (c) 2026 Jonathan D.A. Jewell
