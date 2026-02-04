# Ephapax Compiler

Compiler and interpreter for the ephapax language with linear types.

## Features

- **Lexer**: Tokenizes `.eph` source files
- **Parser**: Builds abstract syntax tree (AST) from tokens
- **Interpreter**: Executes ephapax programs
- **Linear types**: (Type checker in development)

## Usage

### Command Line

```bash
# Run a .eph file
ephapax program.eph

# Execute inline code
ephapax -e 'fn main() { 42 }'
```

### As a Library

```rust
use ephapax_compiler::{run_source, Value};

let source = r#"
    fn double(x) { x + x }
    fn main() { double(21) }
"#;

let result = run_source(source).unwrap();
assert_eq!(result, Value::Int(42));
```

## Language Syntax

### Functions

```ephapax
fn name(param1: type1, param2: type2) -> return_type {
    body
}
```

Type annotations are optional (type inference):

```ephapax
fn double(x) {
    x + x
}
```

### Let Bindings

```ephapax
let variable = expression;
body_using_variable
```

### If Expressions

```ephapax
if condition {
    then_branch
} else {
    else_branch
}
```

### Binary Operations

- Arithmetic: `+`, `-`, `*`, `/`, `%`
- Comparison: `==`, `!=`, `<`, `>`, `<=`, `>=`

### Types

- `i32`: 32-bit integer
- `i64`: 64-bit integer
- `bool`: Boolean

## Examples

### Simple Program

```ephapax
fn main() {
    42
}
```

### Function Call

```ephapax
fn add(x: i32, y: i32) -> i32 {
    x + y
}

fn main() {
    add(10, 20)
}
```

### Conditionals

```ephapax
fn max(a: i32, b: i32) -> i32 {
    if a > b {
        a
    } else {
        b
    }
}

fn main() {
    max(5, 10)
}
```

### Type Compatibility (from types.eph)

```ephapax
fn prim_i32() -> i32 { 2 }
fn prim_i64() -> i32 { 3 }

fn primitives_compatible(a: i32, b: i32) -> bool {
    if a == b {
        true
    } else {
        // I32 -> I64 widening allowed
        if a == 2 {
            if b == 3 {
                true
            } else {
                false
            }
        } else {
            false
        }
    }
}

fn main() {
    primitives_compatible(prim_i32(), prim_i64())
}
```

## Architecture

```
src/
├── tokens.rs        # Lexer
├── ast.rs           # Abstract Syntax Tree
├── parser.rs        # Recursive descent parser
├── interpreter.rs   # Interpreter
├── lib.rs           # Public API
└── main.rs          # CLI binary
```

## Tests

```bash
cargo test
```

All tests pass:
- Lexer: 3 tests
- Parser: 4 tests
- Interpreter: 6 tests
- Integration: 3 tests

## Status

- ✅ Lexer
- ✅ Parser
- ✅ Interpreter
- ⚠️ Type checker (basic, no linear types yet)
- ❌ Linear type checker (planned)
- ❌ WASM backend (planned)

## Linear Types (Planned)

Ephapax will enforce linear types to guarantee:
- Values used exactly once
- No aliasing
- Memory safety without garbage collection
- Provable correctness

The type checker will track:
- Variable usage count
- Move semantics
- Affine types (use at most once)

## License

PMPL-1.0-or-later
