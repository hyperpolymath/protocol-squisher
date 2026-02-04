# Protocol Squisher Examples

This directory contains example projects demonstrating protocol-squisher's capabilities for zero-copy Rust↔Python interoperability.

## Examples Overview

### 1. zero-copy-demo/ ⭐ Start Here
**Concorde-class transport (100% fidelity, 0% overhead)**

Demonstrates perfect type compatibility between Rust and Python:
- i64 ↔ int (both 64-bit signed integers)
- f64 ↔ float (both IEEE 754 double precision)
- String ↔ str (both UTF-8 strings)
- bool ↔ bool (both boolean values)

**Key takeaway:** When types match perfectly, you get direct memory access with ~1ns per field access.

```bash
cd zero-copy-demo
./build.sh
python test.py
```

### 2. mixed-transport/
**Business and Wheelbarrow classes**

Shows what happens when types don't perfectly match:
- **Business class:** Safe widening (i32→i64, f32→f64) with minor overhead
- **Wheelbarrow class:** Narrowing (i64→i32) requires JSON fallback (100-1000x slower)

**Key takeaway:** Avoid narrowing conversions. Safe widening is acceptable.

```bash
cd mixed-transport
# See README.md for analysis examples
```

### 3. rust_python_interop.rs
Basic example showing schema extraction and analysis.

### 4. schema_format_comparison.rs
Demonstrates analyzing different schema formats (Rust, Python, JSON Schema, Protobuf).

## Quick Start

### Analyze a Schema

```bash
# Analyze Rust types
cargo run -p protocol-squisher-cli -- analyze --rust examples/zero-copy-demo/src/lib.rs

# Analyze with detailed output
cargo run -p protocol-squisher-cli -- analyze --rust examples/zero-copy-demo/src/lib.rs --detailed
```

### Check Compatibility

```bash
cargo run -p protocol-squisher-cli -- check \
  --rust examples/zero-copy-demo/src/lib.rs \
  --python examples/zero-copy-demo/models.py
```

### Get Optimization Suggestions

```bash
cargo run -p protocol-squisher-cli -- optimize \
  --rust examples/mixed-transport/src/lib.rs \
  --python examples/mixed-transport/models.py
```

### Generate PyO3 Bindings

```bash
cargo run -p protocol-squisher-cli -- generate \
  --rust examples/zero-copy-demo/src/lib.rs \
  --python examples/zero-copy-demo/models.py \
  --output generated/ \
  --stubs
```

## Transport Class Quick Reference

| Class | Fidelity | Overhead | Examples | Performance |
|-------|----------|----------|----------|-------------|
| **Concorde** | 100% | 0% | i64↔int, f64↔float, String↔str | ~1ns |
| **Business** | 98% | 5% | i32→int, f32→float | ~2-5ns |
| **Economy** | 80% | 25% | Documented minor losses | ~10-50ns |
| **Wheelbarrow** | 50% | 80% | i64→i32, needs JSON | ~100-1000ns |

## Best Practices

### ✅ DO

1. **Match types from the start**
   - Rust i64 ↔ Python int
   - Rust f64 ↔ Python float
   - Rust String ↔ Python str
   - Rust bool ↔ Python bool

2. **Use protocol-squisher analyze early**
   - Run analysis during schema design
   - Fix issues before implementing

3. **Accept Business class when necessary**
   - Safe widening (i32→i64) is OK
   - Minor overhead is acceptable for safety

### ❌ DON'T

1. **Avoid narrowing conversions**
   - i64 → i32 (Wheelbarrow class)
   - f64 → f32 (Wheelbarrow class)
   - Requires JSON fallback (100-1000x slower)

2. **Don't ignore warnings**
   - Generated code includes WARNING comments
   - Wheelbarrow fields have high overhead

3. **Don't assume all conversions are free**
   - Run `protocol-squisher analyze` to verify
   - Check transport classes for all fields

## Building Examples

Most examples are standalone Rust projects with PyO3:

```bash
cd examples/NAME
cargo build --release
python test.py  # If available
```

For PyO3 examples with maturin:

```bash
cd examples/NAME
./build.sh  # Runs maturin develop
python test.py
```

## Example Project Structure

```
examples/NAME/
├── Cargo.toml       # Rust project configuration
├── pyproject.toml   # Python/maturin configuration (if PyO3)
├── README.md        # Example-specific documentation
├── build.sh         # Build script (if needed)
├── src/
│   └── lib.rs       # Rust implementation
├── models.py        # Python type definitions (if applicable)
└── test.py          # Python test/demo script (if applicable)
```

## Next Steps

1. **Start with zero-copy-demo/** to understand Concorde-class transport
2. **Read mixed-transport/** to learn about Business and Wheelbarrow classes
3. **Try the CLI commands** on your own schemas
4. **Run optimization analysis** to improve transport classes

## See Also

- [CLI Documentation](../crates/protocol-squisher-cli/README.md)
- [Transport Classes Explained](../docs/transport-classes.md)
- [Optimization Guide](../docs/optimization.md)
