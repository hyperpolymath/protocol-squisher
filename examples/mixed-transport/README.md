# Mixed Transport Example

This example demonstrates **mixed transport classes** - when some fields are zero-copy (Concorde) but others require conversion (Business) or JSON fallback (Wheelbarrow).

## Transport Classes Overview

| Class | Fidelity | Overhead | Use Case |
|-------|----------|----------|----------|
| **Concorde** | 100% | 0% | Identical types (i64↔int) |
| **Business** | 98% | 5% | Safe widening (i32→i64) |
| **Economy** | 80% | 25% | Documented minor losses |
| **Wheelbarrow** | 50% | 80% | Narrowing (i64→i32), JSON fallback |

## This Example

### Struct with Mixed Transport Classes

```rust
#[derive(Serialize, Deserialize)]
pub struct MixedRecord {
    pub id: i64,           // Concorde: i64 ↔ int ✓
    pub value: i32,        // Business: i32 ↔ int (widening)
    pub timestamp: i64,    // Concorde: i64 ↔ int ✓
    pub score: f32,        // Business: f32 ↔ float (widening)
}
```

**Python side (if we were narrowing):**
```python
class ProblematicRecord(BaseModel):
    id: int        # i64 → int ✓ Concorde
    value: int32   # i64 → int32 ✗ Wheelbarrow (if value was i64 in Rust)
    timestamp: int # i64 → int ✓ Concorde
    score: float32 # f64 → float32 ✗ Wheelbarrow (if score was f64 in Rust)
```

## Analysis Output

```bash
$ protocol-squisher analyze --rust src/lib.rs --python models.py

Schema Compatibility Analysis:
  Overall Transport Class: Business ✓
  Production Ready: Yes (>90% safe conversions)

Field-Level Analysis:
  MixedRecord:
    id: Concorde (100% fidelity, 0% overhead) ✓
    value: Business (98% fidelity, 5% overhead) ⚠
    timestamp: Concorde (100% fidelity, 0% overhead) ✓
    score: Business (98% fidelity, 5% overhead) ⚠

Quality Metrics:
  Zero-copy fields: 2/4 (50%)
  Safe conversions: 4/4 (100%)
  JSON fallback: 0/4 (0%)
  Production readiness: ✓ Yes
```

## Business Class: Safe Widening

Business-class transport occurs when widening numeric types (no data loss):

```rust
// Rust source
pub struct SourceData {
    pub count: i32,   // 32-bit signed
    pub ratio: f32,   // 32-bit float
}
```

```python
# Python target
class TargetData(BaseModel):
    count: int    # Python int is i64 internally (widening!)
    ratio: float  # Python float is f64 internally (widening!)
```

**Result:**
- `count`: i32 → i64 = **Business** (safe widening, minor overhead)
- `ratio`: f32 → f64 = **Business** (safe widening, minor overhead)

**Generated Code:**
```rust
#[pyclass]
pub struct TargetData {
    #[pyo3(get)]
    pub count: i32,  // Getter converts i32 → i64 automatically

    #[pyo3(set)]
    pub set_count(&mut self, value: i64) -> PyResult<()> {
        self.count = value.try_into()
            .map_err(|_| PyErr::new::<PyValueError, _>("count overflow"))?;
        Ok(())
    }
}
```

## Wheelbarrow Class: Narrowing (Avoid!)

Wheelbarrow-class requires JSON fallback due to potential data loss:

```rust
// Rust source (BAD DESIGN)
pub struct BigData {
    pub large_number: i64,  // Can hold values > 2^31
}
```

```python
# Python target (INCOMPATIBLE)
class SmallData(BaseModel):
    large_number: int32  # Can only hold values up to 2^31 - 1
```

**Result:**
- `large_number`: i64 → i32 = **Wheelbarrow** ✗
- Requires JSON serialization/deserialization
- 100-1000x slower than zero-copy
- Risk of runtime errors if value too large

**Generated Code (with WARNING):**
```rust
// ⚠ WARNING: This field uses JSON fallback (Wheelbarrow class)
// Reason: Narrowing conversion i64 → i32 may lose data
impl TargetData {
    pub fn from_rust(source: &SourceData) -> PyResult<Self> {
        let json = serde_json::to_string(&source.large_number)
            .map_err(|e| PyErr::new::<PyValueError, _>(e.to_string()))?;
        let large_number: i32 = serde_json::from_str(&json)
            .map_err(|e| PyErr::new::<PyValueError, _>(e.to_string()))?;
        Ok(Self { large_number })
    }
}
```

## Optimization Suggestions

```bash
$ protocol-squisher optimize --rust src/lib.rs --python models.py

Optimization Opportunities:

HIGH IMPACT:
  1. Widen SmallData.large_number: i32 → i64
     Current: Wheelbarrow (50% fidelity, 80% overhead)
     After: Concorde (100% fidelity, 0% overhead)
     Impact: +25% overall quality

MEDIUM IMPACT:
  2. Consider making optional fields truly optional
     Fields without values could avoid serialization entirely

Estimated Improvement: 25% fewer JSON conversions
```

## Key Takeaways

✅ **Business class is OK** - Safe widening (i32→i64, f32→f64) has minimal overhead

⚠️ **Avoid Wheelbarrow class** - Narrowing (i64→i32, f64→f32) requires JSON fallback

🎯 **Best Practice:** Design schemas with matching types from the start

## Running This Example

```bash
# Analyze transport classes
cargo run -p protocol-squisher-cli -- analyze --rust examples/mixed-transport/src/lib.rs

# Get optimization suggestions
cargo run -p protocol-squisher-cli -- optimize --rust examples/mixed-transport/src/lib.rs --python examples/mixed-transport/models.py

# Build and test
cd examples/mixed-transport
./build.sh
python test.py
```

## See Also

- `examples/zero-copy-demo/` - Concorde-class only (best performance)
- `examples/optimization/` - Before/after optimization examples
