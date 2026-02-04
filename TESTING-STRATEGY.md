# Testing Strategy: Every Possible Possibility

**Goal:** Achieve comprehensive coverage of all conversion scenarios, edge cases, and failure modes.

## Current Status: 180 tests ✓

See [TEST-COVERAGE.md](TEST-COVERAGE.md) for detailed breakdown.

## Testing Every Possibility: The Matrix

To test "every possible possibility," we need to cover the **Cartesian product** of:
- Source types × Target types × Transport classes × Edge cases

### 1. Type Combination Matrix (15 primitive × 15 primitive = 225 combinations)

#### Primitive Types
- **Integers**: i8, i16, i32, i64, i128, u8, u16, u32, u64, u128
- **Floats**: f32, f64
- **Other**: bool, char, String

#### Current Coverage:
```
Source   Target   Transport Class   Tested?
i64      i64      Concorde          ✓
i64      i32      Wheelbarrow       ✓
i32      i64      Business          ✓
f64      f64      Concorde          ✓
f64      f32      Wheelbarrow       ✓
String   String   Concorde          ✓
bool     bool     Concorde          ✓
...      ...      ...               ⚠️ (210 combinations untested)
```

#### Needed Tests:
```rust
// Auto-generate comprehensive primitive test matrix
#[cfg(test)]
mod primitive_matrix_tests {
    use proptest::prelude::*;

    // Test all integer narrowing combinations
    proptest! {
        #[test]
        fn test_all_integer_conversions(
            i8_val in any::<i8>(),
            i16_val in any::<i16>(),
            // ... all primitive types
        ) {
            // Test i8 → i16, i8 → i32, ... (all 100 integer pairs)
            assert_transport_class(i8_val, i16_val as i8, TransportClass::Business);
            // ...
        }
    }
}
```

**Estimated tests needed:** 225 property tests (one per type pair)

---

### 2. Container Type Matrix

#### Container Types
- `Option<T>`
- `Vec<T>`
- `HashMap<K, V>`
- `HashSet<T>`
- `Tuple(T1, T2, ...)`

#### Nested Containers (exponential growth!)
- `Option<Vec<T>>`
- `Vec<Option<T>>`
- `HashMap<K, Vec<V>>`
- `Vec<HashMap<K, V>>`
- ... (1000s of combinations)

#### Current Coverage:
```
Container Type           Tested?
Option<i64>              ✓
Vec<i64>                 ✓
HashMap<String, i64>     ✓
Option<Vec<i64>>         ✗
Vec<Vec<i64>>            ✗
HashMap<K, Vec<V>>       ✗
```

#### Needed Tests:
```rust
#[test]
fn test_nested_containers() {
    // 2-level nesting
    test_conversion::<Option<Vec<i64>>>();
    test_conversion::<Vec<Option<String>>>();
    test_conversion::<HashMap<String, Vec<Person>>>();

    // 3-level nesting
    test_conversion::<Option<Vec<HashMap<String, Person>>>>();
}
```

**Estimated tests needed:** 50-100 container combination tests

---

### 3. Struct/Enum Combinations

#### Struct Variations
- Empty struct
- Single field
- Multiple fields (2-10)
- Generic structs
- Recursive structs
- Structs with lifetimes

#### Enum Variations
- Unit variants
- Tuple variants
- Struct variants
- Generic enums
- Nested enums

#### Current Coverage:
```
Type Pattern                 Tested?
struct Point { x: i64 }      ✓
struct Person { ... }        ✓
enum Status { ... }          ✓
struct Node<T> { ... }       ✗
struct Tree<'a> { ... }      ✗
```

#### Needed Tests:
```rust
#[test]
fn test_struct_variations() {
    // Generic structs
    test_struct::<Point<i64>>();
    test_struct::<Point<f64>>();

    // Recursive structs
    struct Node { value: i64, next: Option<Box<Node>> }
    test_conversion::<Node>();
}
```

**Estimated tests needed:** 30-40 structural variation tests

---

### 4. Edge Cases & Boundary Conditions

#### Integer Boundaries
```rust
#[test]
fn test_integer_boundaries() {
    // Test all boundary values
    assert_converts(i64::MIN, i32::MIN); // Should fail (overflow)
    assert_converts(i64::MAX, i32::MAX); // Should fail (overflow)
    assert_converts(i32::MIN, i64::MIN); // Should succeed (widening)
    // ... test all min/max combinations
}
```

#### String Edge Cases
```rust
#[test]
fn test_string_edge_cases() {
    test_conversion(""); // Empty
    test_conversion("a"); // Single char
    test_conversion("🦀"); // Unicode
    test_conversion(&"a".repeat(1_000_000)); // Large string
    test_conversion("\0"); // Null byte
}
```

#### Container Edge Cases
```rust
#[test]
fn test_container_edge_cases() {
    test_conversion(Vec::<i64>::new()); // Empty vec
    test_conversion(vec![i64::MAX]); // Boundary value
    test_conversion((0..1_000_000).collect::<Vec<_>>()); // Large vec
}
```

**Estimated tests needed:** 50-75 edge case tests

---

### 5. Error Paths & Failure Modes

#### Schema Analysis Errors
```rust
#[test]
fn test_malformed_schemas() {
    // Invalid Rust syntax
    assert_err(analyze("pub struct {}}"));

    // Unsupported types
    assert_err(analyze("pub struct Foo { ptr: *const i32 }"));

    // Circular references
    struct A { b: B }
    struct B { a: A }
    assert_err(analyze_cycle());
}
```

#### Conversion Errors
```rust
#[test]
fn test_conversion_errors() {
    // Narrowing overflow
    assert_err(convert(i64::MAX, i32::MAX));

    // Invalid UTF-8
    assert_err(convert_bytes(&[0xFF, 0xFE]));

    // Missing required field
    assert_err(convert_partial_struct());
}
```

**Estimated tests needed:** 25-30 error path tests

---

### 6. Performance & Stress Tests

#### Large Schema Tests
```rust
#[test]
fn test_large_schemas() {
    // Schema with 1000 types
    let schema = generate_schema(1000);
    let analysis = analyze_schemas(&schema, &schema);
    assert!(analysis.completed_in_ms < 5000); // 5 second budget
}
```

#### Deep Nesting Tests
```rust
#[test]
fn test_deep_nesting() {
    // Vec<Vec<Vec<...<i64>>>> (100 levels deep)
    type DeepVec = Vec<Vec<Vec<...>>>;
    assert!(can_analyze::<DeepVec>());
}
```

#### Memory Tests
```rust
#[test]
fn test_memory_usage() {
    // Analyze 10k schemas in sequence
    for _ in 0..10_000 {
        let schema = generate_random_schema();
        analyze(schema);
    }
    // Assert no memory leak
    assert!(current_memory() < initial_memory * 1.1);
}
```

**Estimated tests needed:** 10-15 performance tests

---

### 7. Property-Based Testing (QuickCheck/PropTest)

#### Round-Trip Properties
```rust
proptest! {
    #[test]
    fn prop_round_trip_preserves_value(val: i64) {
        let rust_val = val;
        let python_val = to_python(rust_val);
        let rust_val2 = from_python(python_val);
        assert_eq!(rust_val, rust_val2);
    }

    #[test]
    fn prop_transport_class_monotonic(
        source in any_rust_type(),
        target in any_rust_type()
    ) {
        // Widening should never make transport class worse
        let class1 = transport_class(source, target);
        let class2 = transport_class(widen(source), target);
        assert!(class2 <= class1); // Better or same
    }
}
```

#### Invariant Properties
```rust
proptest! {
    #[test]
    fn prop_concorde_means_zero_overhead(
        schema in arbitrary_schema()
    ) {
        if schema.transport_class == Concorde {
            assert_eq!(schema.overhead_percentage, 0.0);
            assert_eq!(schema.fidelity_percentage, 100.0);
        }
    }
}
```

**Estimated tests needed:** 15-20 property tests

---

### 8. Integration & E2E Tests

#### Real PyO3 Compilation
```rust
#[test]
fn test_real_pyo3_compilation() {
    // Generate bindings
    let code = generate(&rust_schema, &python_schema);

    // Write to temp file
    let temp_file = write_temp(code);

    // Actually compile with rustc
    let result = Command::new("rustc")
        .args(&["--crate-type", "cdylib", temp_file])
        .output();

    assert!(result.success());
}
```

#### Python Runtime Tests
```python
# tests/runtime/test_real_conversion.py
def test_actual_python_import():
    import protocol_squisher_bindings

    # Create Rust object from Python
    point = protocol_squisher_bindings.Point(x=10, y=20)
    assert point.x == 10

    # Verify zero-copy (same memory address)
    addr1 = id(point.x)
    point.x = 15
    addr2 = id(point.x)
    # ... (complex but verifies actual zero-copy)
```

**Estimated tests needed:** 5-10 real runtime tests

---

## Complete Test Plan

### Test Count Summary
| Category | Current | Needed | Total Target |
|----------|---------|--------|--------------|
| Primitive matrix | 20 | 205 | 225 |
| Container combinations | 10 | 90 | 100 |
| Struct/Enum variations | 15 | 25 | 40 |
| Edge cases | 10 | 65 | 75 |
| Error paths | 5 | 25 | 30 |
| Performance | 0 | 15 | 15 |
| Property tests | 0 | 20 | 20 |
| Integration/E2E | 7 | 8 | 15 |
| CLI tests | 0 | 20 | 20 |
| **TOTAL** | **180** | **360** | **540** |

### Priority Order

#### Phase 1: Foundation (Now - Week 1)
1. ✓ Primitive matrix (property tests) - 50 tests
2. ✓ Container combinations - 30 tests
3. ✓ Edge cases (boundaries) - 25 tests

**Target:** 285 tests (+105)

#### Phase 2: Robustness (Week 2-3)
4. ✓ Error path coverage - 30 tests
5. ✓ Struct/Enum variations - 25 tests
6. ✓ CLI integration tests - 20 tests

**Target:** 360 tests (+75)

#### Phase 3: Quality (Week 4)
7. ✓ Property-based tests - 20 tests
8. ✓ Performance benchmarks - 15 tests
9. ✓ Real runtime integration - 8 tests

**Target:** 403 tests (+43)

#### Phase 4: Comprehensive (Ongoing)
10. ✓ Fuzzing integration
11. ✓ Mutation testing
12. ✓ Coverage analysis (aim for 95%+)

**Target:** 540+ tests

---

## Implementation Strategy

### 1. Auto-Generate Test Matrix
```bash
# Create test generator
cargo install protocol-squisher-test-gen

# Generate all primitive combinations
protocol-squisher-test-gen primitives > tests/generated/primitives.rs

# Generate container combinations
protocol-squisher-test-gen containers > tests/generated/containers.rs
```

### 2. Property Test Framework
```toml
[dev-dependencies]
proptest = "1.4"
quickcheck = "1.0"
```

### 3. Fuzzing Setup
```bash
# Install cargo-fuzz
cargo install cargo-fuzz

# Create fuzz targets
cargo fuzz init

# Fuzz schema parsing
cargo fuzz run parse_schema

# Fuzz transport class analysis
cargo fuzz run analyze_compatibility
```

### 4. Coverage Measurement
```bash
# Install coverage tool
cargo install cargo-llvm-cov

# Run with coverage
cargo llvm-cov --workspace --html

# Open report
open target/llvm-cov/html/index.html

# Aim for 95%+ line coverage
```

---

## Test Automation

### CI/CD Pipeline
```yaml
# .github/workflows/comprehensive-tests.yml
name: Comprehensive Test Suite

on: [push, pull_request]

jobs:
  unit-tests:
    runs-on: ubuntu-latest
    steps:
      - run: cargo test --workspace

  property-tests:
    runs-on: ubuntu-latest
    steps:
      - run: cargo test --workspace --features proptest

  integration-tests:
    runs-on: ubuntu-latest
    steps:
      - run: cargo test -p protocol-squisher-integration-tests

  fuzz-tests:
    runs-on: ubuntu-latest
    timeout-minutes: 30
    steps:
      - run: cargo fuzz run --all -- -max_total_time=1800

  coverage:
    runs-on: ubuntu-latest
    steps:
      - run: cargo llvm-cov --workspace --html
      - run: |
          COVERAGE=$(cargo llvm-cov report --summary-only | grep TOTAL | awk '{print $10}')
          if (( $(echo "$COVERAGE < 95.0" | bc -l) )); then
            echo "Coverage $COVERAGE% is below 95%"
            exit 1
          fi
```

---

## Success Criteria

### Definition of "Every Possibility Tested"

✅ **Primitive Types**: All 225 type pair combinations tested
✅ **Containers**: All common nesting patterns (2-3 levels deep)
✅ **Structures**: All variation patterns (generic, recursive, etc.)
✅ **Edge Cases**: All boundary conditions and special values
✅ **Error Paths**: All failure modes have explicit tests
✅ **Properties**: Core invariants proven with randomized inputs
✅ **Performance**: No regressions, stays within budgets
✅ **Integration**: Real Rust↔Python conversion works
✅ **Coverage**: >95% line coverage, >90% branch coverage
✅ **Fuzzing**: 24hr continuous fuzzing finds no crashes

### Current Progress
- [x] 180 tests passing ✓
- [ ] 540 total tests (33% complete)
- [ ] 95% coverage (current: ~75%)
- [ ] Fuzzing setup
- [ ] All invariants property-tested

**Next milestone:** 285 tests (Phase 1 complete)
