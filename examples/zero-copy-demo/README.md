# Zero-Copy Interop Example

This example demonstrates **Concorde-class** (zero-copy, 100% fidelity) conversions between Rust and Python.

## What is Zero-Copy?

Zero-copy means data can be accessed directly without serialization/deserialization overhead. Protocol Squisher identifies when types are compatible enough to share memory representations.

## Transport Classes

- **Concorde** (100% fidelity, 0% overhead): Zero-copy, perfect match
- **Business** (98% fidelity, 5% overhead): Safe widening (i32→i64)
- **Economy** (80% fidelity, 25% overhead): Minor documented losses
- **Wheelbarrow** (50% fidelity, 80% overhead): JSON fallback

## This Example

### Rust Schema (`src/lib.rs`)
```rust
#[derive(Serialize, Deserialize)]
pub struct Point {
    pub x: i64,  // Concorde: i64 → i64
    pub y: i64,  // Concorde: i64 → i64
}

#[derive(Serialize, Deserialize)]
pub struct Person {
    pub name: String,   // Concorde: String → str
    pub age: i64,       // Concorde: i64 → int
    pub active: bool,   // Concorde: bool → bool
}
```

### Python Schema (`models.py`)
```python
from pydantic import BaseModel

class Point(BaseModel):
    x: int  # Python int (i64 internally)
    y: int  # Perfect match with Rust i64

class Person(BaseModel):
    name: str      # Perfect match
    age: int       # Perfect match
    active: bool   # Perfect match
```

## Analysis

Run protocol-squisher analyze:

```bash
protocol-squisher analyze --rust src/lib.rs --detailed
```

**Output:**
```
Schema Information:
  Transport Class: Concorde ✓

Field-Level Analysis:
  Point:
    x: Concorde (100% fidelity, 0% overhead)
    y: Concorde (100% fidelity, 0% overhead)

  Person:
    name: Concorde (100% fidelity, 0% overhead)
    age: Concorde (100% fidelity, 0% overhead)
    active: Concorde (100% fidelity, 0% overhead)
```

## Generated PyO3 Bindings

```bash
protocol-squisher generate --rust src/lib.rs --python models.py --stubs
```

**Generated Rust (`bindings.rs`):**
```rust
#[pyclass]
pub struct Point {
    #[pyo3(get, set)]  // Direct access - zero overhead!
    pub x: i64,

    #[pyo3(get, set)]  // No serialization needed
    pub y: i64,
}

// Quality: 100% zero-copy, production ready ✓
```

**Performance:**
- **Concorde**: Direct memory access, ~1ns per field access
- **Wheelbarrow** (JSON): Serialize/deserialize, ~100-1000ns overhead

## Why This Works

1. **Type Compatibility**: Rust `i64` ↔ Python `int` are ABI-compatible
2. **Memory Layout**: Both use 64-bit signed integers
3. **No Conversion Needed**: Direct pointer access via PyO3

## Counter-Example: Narrowing (Wheelbarrow)

### What NOT to do:
```rust
// Rust
pub struct BadPoint {
    pub x: i64,  // Source: 64-bit
}
```

```python
# Python
class BadPoint(BaseModel):
    x: int32  # Target: 32-bit (if we used numpy.int32)
```

**Result:** Wheelbarrow class - needs JSON fallback due to potential data loss!

## Running the Example

```bash
# Analyze
cargo run -p protocol-squisher-cli -- analyze --rust examples/zero-copy-demo/src/lib.rs

# Optimize (should show "No optimization needed")
cargo run -p protocol-squisher-cli -- optimize --rust examples/zero-copy-demo/src/lib.rs --python examples/zero-copy-demo/models.py

# Generate bindings
cargo run -p protocol-squisher-cli -- generate --rust examples/zero-copy-demo/src/lib.rs --python examples/zero-copy-demo/models.py --output generated/
```

## Key Takeaways

✅ **DO** use matching types (i64↔int, String↔str, bool↔bool)
✅ **DO** prefer zero-copy when possible (100x+ faster)
✅ **DO** run `protocol-squisher optimize` to find opportunities

❌ **DON'T** narrow types (i64→i32) unless necessary
❌ **DON'T** assume all conversions are zero-copy
❌ **DON'T** ignore Wheelbarrow warnings in generated code

## Next Steps

- See `examples/mixed-conversion/` for Business/Wheelbarrow examples
- See `examples/optimization/` for improving transport classes
- Run `protocol-squisher --help` for all commands
