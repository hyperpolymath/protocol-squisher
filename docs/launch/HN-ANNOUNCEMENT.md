# Show HN: Protocol Squisher – Universal Protocol Interoperability with Formal Guarantees

**TL;DR:** Automatic adapter synthesis between any two serialization formats. If it compiles, it carries. 742 tests, formal proofs in Agda/Lean, 11 format analyzers, v1.0.0 just released.

---

## The Problem

You have a Rust service using serde. Your colleague's Python service uses Pydantic. You need them to talk.

Current options:
1. Write manual FFI glue (hours/days, error-prone)
2. JSON as lingua franca (slow, manual conversions)
3. Rewrite one side (expensive, political)
4. Give up

**The real problem:** Every serialization format pair needs custom bridge code. With N formats, that's O(N²) adapters to maintain.

## The Solution

Protocol Squisher analyzes schema pairs and synthesizes the minimum viable adapter with provable correctness guarantees.

```bash
$ protocol-squisher check --rust lib.rs --python models.py

Analysis Results:
  Transport Class: Concorde (100% fidelity, 0% overhead)

Field Compatibility:
  ✓ user_id: i64 ↔ int (native mapping)
  ✓ balance: f64 ↔ float (IEEE 754 compatible)
  ✓ name: String ↔ str (UTF-8)
  ✓ active: bool ↔ bool (identical)

TRANSPORT VIABLE: Zero-copy possible

$ protocol-squisher generate --rust lib.rs --python models.py --output ./

Generated PyO3 bindings:
  ✓ lib.rs (657 lines)
  ✓ models.pyi (type stubs)
  ✓ tests.py (property-based tests)
```

**Result:** Direct memory access between Rust and Python. ~1ns per field. No serialization overhead.

## Transport Classes

Every schema pair gets classified:

| Class | Fidelity | Overhead | Example |
|-------|----------|----------|---------|
| **Concorde** | 100% | 0% | i64↔int, f64↔float |
| **Business** | 98% | 5% | i32→i64 (safe widening) |
| **Economy** | 80% | 25% | Documented minor losses |
| **Wheelbarrow** | 50% | 80% | i64→i32 (needs JSON fallback) |

The CLI tells you which class you get *before* generating code.

## The Invariant

```
For any valid input x in format A,
there exists a valid output y in format B
such that squish(x) = y.
```

**"If it compiles, it carries."**

Even if slow. Even if lossy. But it *will* transport.

We achieve this through:
1. **Canonical IR** - Every format maps to ephapax intermediate representation
2. **Compatibility analysis** - We prove transport is possible before generating
3. **JSON fallback** - When all else fails, JSON becomes the wheelbarrow
4. **Property-based testing** - Generated adapters include exhaustive test suites

## Formal Verification

Core theorems proven in Agda (Concorde Safety cross-validated in Lean):

1. **Concorde Safety** (fully verified): Identical types → lossless bijection
2. **Container Propagation** (fully verified): Container class = worst element class
3. **Wheelbarrow Necessity** (partial): Narrowing conversions require fallback
4. **Carries Invariant** (partial): Every schema pair has an adapter

Proofs: https://github.com/hyperpolymath/protocol-squisher/tree/main/proofs

## Real-World Example

**Before (manual FFI):**
```rust
#[pyclass]
struct User {
    #[pyo3(get, set)]
    user_id: i64,
    #[pyo3(get, set)]
    balance: f64,
    // ... 50 lines of boilerplate
}

#[pymethods]
impl User {
    #[new]
    fn new(user_id: i64, balance: f64) -> Self { /* ... */ }
    // ... 30 more lines
}
```

**After (protocol-squisher):**
```rust
#[derive(Serialize, Deserialize)]
struct User {
    user_id: i64,
    balance: f64,
}
```

Generated code handles all FFI, type conversions, and includes property tests.

## Current Status

**v1.0.0 Released**
- ✅ 742 tests passing
- ✅ 11 format analyzers: Rust, Python, Protobuf, Thrift, Avro, MessagePack, FlatBuffers, Cap'n Proto, Bebop, ReScript, JSON Schema
- ✅ CLI with analysis, optimization suggestions, code generation
- ✅ Formal proofs in Agda/Lean (2 complete, 2 partial)
- ✅ Zero-copy benchmarks (~1ns Concorde, ~100-1000ns Wheelbarrow)

## Try It

```bash
git clone https://github.com/hyperpolymath/protocol-squisher
cd protocol-squisher/examples/zero-copy-demo
./build.sh
python test.py  # See ~1ns field access

# Or install CLI
cargo install --path crates/protocol-squisher-cli
protocol-squisher --help
```

**Documentation:**
- CLI Guide: https://github.com/hyperpolymath/protocol-squisher/blob/main/docs/CLI-GUIDE.adoc
- Examples: https://github.com/hyperpolymath/protocol-squisher/tree/main/examples
- Formal Proofs: https://github.com/hyperpolymath/protocol-squisher/tree/main/proofs

## Why This Matters

Polyglot systems are the norm. Every microservice boundary is a potential serialization mismatch. Manual adapters are:
- Time-consuming
- Error-prone
- Unmaintained (bit rot)

Protocol Squisher makes format interop a build step, not a maintenance burden.

## Limitations (We're Honest)

1. **Wheelbarrow class is slow** - Narrowing conversions need JSON (100-1000x overhead)
2. **Analysis requires schemas** - No runtime schema inference yet
3. **Optimization coverage varies by format pair** - Some pairs remain Wheelbarrow-class until optimizer/synthesis tuning improves

We document losses upfront. No surprises.

## Contributing

We need:
- Real-world schema examples that break our analysis
- Edge cases in formal proofs (help us finish the partial proofs!)
- Performance optimizations
- New format analyzers (GraphQL, gRPC, Excel, etc.)

Issues: https://github.com/hyperpolymath/protocol-squisher/issues

## License

PMPL-1.0-or-later (Palimpsest License)

---

Built by [@hyperpolymath](https://github.com/hyperpolymath). Inspired by every polyglot developer who's cursed at FFI boilerplate.

Questions? Comments? Found an edge case that breaks the invariant? Let's hear it.
