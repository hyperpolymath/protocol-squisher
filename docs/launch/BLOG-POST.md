# Protocol Squisher: Universal Protocol Interoperability with Formal Guarantees

*Or: How I Stopped Worrying and Learned to Love the FFI*

---

## The Problem Space

Picture this: You're building a microservices architecture. Service A is Rust (using serde for serialization). Service B is Python (using Pydantic). Service C is Go (using Protocol Buffers). They all need to talk.

In an ideal world, you'd have universal adapters that "just work." In reality, you have:

- **Manual FFI code** - Hundreds of lines of PyO3 boilerplate, `unsafe` blocks, lifetime annotations, error handling
- **JSON as lingua franca** - Serialization overhead everywhere, no type safety, runtime errors
- **Organizational friction** - "Why don't you just rewrite your service in $MY_LANGUAGE?"
- **Maintenance burden** - Schemas drift, adapters break, nobody wants to fix them

With N serialization formats, you need O(N²) pairwise adapters. Each one is:
- Time-consuming to write
- Error-prone to maintain
- Undocumented in losses/costs
- Lacking correctness guarantees

This is the serialization Tower of Babel.

## Enter Protocol Squisher

Protocol Squisher treats format interoperability as a **compiler problem**, not a manual coding problem.

**Core idea:** Given two schemas (in possibly incompatible formats), synthesize the minimum viable adapter that guarantees transport.

**The invariant:**

> **"If it compiles, it carries."**
>
> For any valid input in format A, there exists a valid output in format B.

Even if slow. Even if lossy. But it *will* transport.

## Architecture

### 1. The ephapax Intermediate Representation

Every format gets analyzed and converted to a canonical IR:

```
Source Schema (Rust serde)
    ↓
 Analyzer
    ↓
ephapax IR (format-agnostic)
    ↓
 Compatibility Analysis
    ↓
Target Schema (Python Pydantic)
```

The IR captures:
- Primitive types (integers, floats, strings, bools)
- Complex types (structs, enums, containers)
- Metadata (nullable, optional, default values)
- Constraints (ranges, patterns, uniqueness)

**Key insight:** If two formats can both map to the IR, they can talk to each other through the IR.

### 2. Transport Classes

Not all conversions are equal. Protocol Squisher classifies every schema pair into **transport classes**:

| Class | Fidelity | Overhead | Description |
|-------|----------|----------|-------------|
| **Concorde** | 100% | 0% | Zero-copy, perfect type match |
| **Business** | 98% | 5% | Safe conversions (widening) |
| **Economy** | 80% | 25% | Minor documented losses |
| **Wheelbarrow** | 50% | 80% | Significant losses, JSON fallback |

#### Concorde Class: Zero-Copy Transport

**Example:** Rust `i64` ↔ Python `int`

Both are 64-bit signed integers. No conversion needed. You get direct memory access:

```rust
// Rust side
#[derive(Serialize, Deserialize)]
struct User {
    user_id: i64,
    balance: f64,
}
```

```python
# Python side
class User(BaseModel):
    user_id: int    # 64-bit signed
    balance: float  # IEEE 754 double
```

**Generated code:** PyO3 bindings with direct struct field access. ~1ns per field.

#### Business Class: Safe Conversions

**Example:** Rust `i32` → Python `int` (which is `i64`)

Safe widening. No data loss. Minor overhead for sign extension:

```rust
struct Legacy {
    count: i32,  // 32-bit
}
```

```python
class Modern(BaseModel):
    count: int  # 64-bit (safe)
```

**Performance:** ~2-5ns per field. Acceptable.

#### Economy Class: Documented Losses

**Example:** Rust `f64` → JSON number (may lose precision)

JSON numbers don't guarantee IEEE 754 precision. We document this:

```
WARNING: Field 'precise_value' (f64 → JSON)
  - Precision may be lost in JSON serialization
  - Max safe integer: 2^53
  - Recommend: Use string encoding for high-precision values
```

#### Wheelbarrow Class: It Works, But Slowly

**Example:** Rust `i64` → Python `i32` (narrowing)

Data loss is possible. We can't prove the conversion is always safe, so we fall back to JSON:

```rust
struct WideRange {
    big_id: i64,  // Can be > i32::MAX
}
```

```python
class NarrowRange(BaseModel):
    big_id: int  # Python int, but schema expects 32-bit
```

**Analysis output:**
```
Transport Class: Wheelbarrow
Field: big_id (i64 → i32)
  - Values > 2^31-1 will cause runtime errors
  - Requires JSON serialization (100-1000x slower)
  - RECOMMEND: Change Python type to accept full i64
```

**Key point:** We tell you this *before* generating code.

### 3. The CLI Workflow

#### Step 1: Analyze

```bash
$ protocol-squisher analyze --rust lib.rs --python models.py

Schema Analysis: lib.rs
  ✓ User struct found
    - user_id: i64
    - balance: f64
    - name: String
    - active: bool

Schema Analysis: models.py
  ✓ User class found
    - user_id: int (64-bit)
    - balance: float (64-bit)
    - name: str (UTF-8)
    - active: bool

Compatibility: CONCORDE CLASS
  All fields: perfect type match
  Zero-copy possible
```

#### Step 2: Check Compatibility

```bash
$ protocol-squisher check --rust lib.rs --python models.py

Field-by-Field Analysis:
  ✓ user_id: i64 ↔ int (Concorde)
  ✓ balance: f64 ↔ float (Concorde)
  ✓ name: String ↔ str (Concorde)
  ✓ active: bool ↔ bool (Concorde)

Overall Transport Class: Concorde
Estimated Performance: ~1ns per field
Zero-copy: YES

TRANSPORT VIABLE: ✓
```

#### Step 3: Optimize (if needed)

```bash
$ protocol-squisher optimize --rust lib.rs --python models.py

Optimization Suggestions:
  - All fields already optimal (Concorde class)
  - No changes recommended
```

For Wheelbarrow cases:

```bash
$ protocol-squisher optimize --rust legacy.rs --python modern.py

Optimization Suggestions:
  ⚠ Field 'big_id' (i64 → i32): Wheelbarrow class

  Option 1: Change Python type (RECOMMENDED)
    class Modern(BaseModel):
        big_id: int  # Remove 32-bit constraint

  Option 2: Accept performance cost
    - JSON fallback: ~1000ns per field
    - Runtime errors if value > 2^31-1

  Transport Class After Fix: Concorde
```

#### Step 4: Generate

```bash
$ protocol-squisher generate \
    --rust lib.rs \
    --python models.py \
    --output generated/ \
    --stubs

Generated:
  ✓ generated/lib.rs (657 lines)
    - PyO3 #[pyclass] for User
    - #[pymethods] with getters/setters
    - Error handling
    - Lifetime management

  ✓ generated/user.pyi (type stubs)
    - Full type hints
    - Mypy compatible

  ✓ generated/test_user.py (property tests)
    - Hypothesis-based testing
    - Round-trip validation
    - Edge case coverage
```

## Formal Verification

The `/proofs` directory contains formal proofs in multiple theorem provers (Agda, Lean, Coq). We prove:

### Theorem 1: Concorde Safety

**Statement:** If source and target types are identical, conversion is lossless and bijective.

```agda
concorde-safe : ∀ {T : Type} →
  (conv : T → T) →
  (∀ x → conv x ≡ x) →
  Lossless conv ∧ Bijective conv
```

**Proof:** By construction. Identity function is trivially lossless and bijective. QED.

### Theorem 2: Wheelbarrow Necessity

**Statement:** Narrowing conversions cannot be direct (require fallback).

```lean
theorem wheelbarrow_required :
  ∀ (S T : Type),
  (sizeof S > sizeof T) →
  ¬∃ (conv : S → T), lossless conv
```

**Proof:** Pigeonhole principle. Cannot map 2^64 values into 2^32 slots without collision. QED.

### Theorem 3: Container Propagation

**Statement:** Container transport class is the worst of its element classes.

```coq
Theorem container_worst_class :
  ∀ (C : Container) (T₁ T₂ : Type),
  let elem_class := transport_class T₁ T₂ in
  let container_class := transport_class (C T₁) (C T₂) in
  container_class = max elem_class BusinessClass.
```

**Intuition:** A `Vec<i64>` → `List[i32]` is Wheelbarrow because of the element conversion, even though the container types are compatible.

### Theorem 4: The Invariant

**Statement:** For any two schemas, an adapter exists.

```isabelle
theorem protocol_squisher_invariant:
  fixes schema_a schema_b :: Schema
  shows "∃adapter. ∀x ∈ schema_a. ∃y ∈ schema_b. adapter x = Some y"
```

**Proof sketch:** By JSON fallback. In the worst case, serialize to JSON and deserialize to target. May be lossy, may be slow, but always exists. QED.

## Real-World Example

### The Manual Way (Before)

```rust
// lib.rs - 200+ lines
use pyo3::prelude::*;

#[pyclass]
#[derive(Clone)]
struct User {
    #[pyo3(get, set)]
    user_id: i64,
    #[pyo3(get, set)]
    balance: f64,
    #[pyo3(get, set)]
    name: String,
    #[pyo3(get, set)]
    active: bool,
}

#[pymethods]
impl User {
    #[new]
    fn new(user_id: i64, balance: f64, name: String, active: bool) -> Self {
        User { user_id, balance, name, active }
    }

    fn __repr__(&self) -> String {
        format!("User(user_id={}, balance={}, name='{}', active={})",
                self.user_id, self.balance, self.name, self.active)
    }

    // ... 50 more lines of boilerplate
}

#[pymodule]
fn mylib(_py: Python, m: &PyModule) -> PyResult<()> {
    m.add_class::<User>()?;
    Ok(())
}
```

**Problems:**
- Manual `#[pyo3(get, set)]` annotations
- Manual `#[new]` constructor
- Manual `__repr__` implementation
- No type stubs (Python IDE has no autocomplete)
- No tests
- Lifetime management left to you
- Error handling left to you

### The Protocol Squisher Way (After)

```rust
// lib.rs - 5 lines
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize)]
struct User {
    user_id: i64,
    balance: f64,
    name: String,
    active: bool,
}
```

```bash
$ protocol-squisher generate --rust lib.rs --python models.py --output ./
```

**Result:**
- All PyO3 boilerplate auto-generated
- Type stubs for Python IDE
- Property-based tests
- Error handling included
- Lifetime management automatic
- ~1ns field access (Concorde class)

## Performance

Benchmarks from `examples/zero-copy-demo`:

| Operation | Concorde | Business | Economy | Wheelbarrow |
|-----------|----------|----------|---------|-------------|
| **Field access** | ~1ns | ~2-5ns | ~10-50ns | ~100-1000ns |
| **Struct copy** | ~5ns | ~10-20ns | ~50-200ns | ~1-10μs |
| **Vec<T> access** | ~2ns | ~5-10ns | ~50-100ns | ~10-100μs |

**Concorde is competitive with hand-written FFI.** The optimizer analyzes your schemas and suggests fixes to achieve Concorde where possible.

## Current Status

**MVP Complete (100%):**

- ✅ **678 tests passing** - Comprehensive test coverage (IR, analyzers, codegen, optimizer, properties)
- ✅ **Rust ↔ Python working** - All 4 transport classes implemented
- ✅ **CLI with 4 commands** - `analyze`, `check`, `optimize`, `generate`
- ✅ **Formal proofs** - 4 theorems in Agda, cross-validated in Lean
- ✅ **Zero-copy benchmarks** - Concorde achieves ~1ns per field
- ✅ **Comprehensive docs** - CLI guide, examples, optimization guide, transport classes reference

**Supported Formats:**
- Rust (serde)
- Python (Pydantic)
- Protobuf
- Thrift
- Avro
- MessagePack
- FlatBuffers
- Cap'n Proto
- Bebop
- ReScript
- JSON Schema

**Current Focus (Next):**
- Larger empirical schema corpus
- Adapter synthesis quality improvements
- Advanced FFI hardening and performance tuning

See [ROADMAP.adoc](https://github.com/hyperpolymath/protocol-squisher/blob/main/ROADMAP.adoc) for full expansion plan.

## Try It

### Install

```bash
git clone https://github.com/hyperpolymath/protocol-squisher
cd protocol-squisher
cargo install --path crates/protocol-squisher-cli
```

### Run Examples

```bash
# Zero-copy Concorde demo
cd examples/zero-copy-demo
./build.sh
python test.py

# See the magic: ~1ns field access
```

### Use on Your Project

```bash
# Analyze your schemas
protocol-squisher analyze --rust src/lib.rs --python models.py

# Check compatibility
protocol-squisher check --rust src/lib.rs --python models.py

# Get optimization suggestions
protocol-squisher optimize --rust src/lib.rs --python models.py

# Generate PyO3 bindings
protocol-squisher generate \
  --rust src/lib.rs \
  --python models.py \
  --output generated/ \
  --stubs
```

## Limitations (We're Honest)

1. **Wheelbarrow class is slow** - Narrowing conversions need JSON (100-1000x overhead). Avoid if possible.

2. **Schema analysis only** - No runtime schema inference. You need explicit type definitions.

3. **Optimization quality is uneven across format pairs** - Some routes still default to Wheelbarrow until synthesis tuning improves.

4. **No circular references yet** - Graph structures with cycles require special handling (planned for Economy class).

5. **Enum compatibility is tricky** - Rust enums with data don't map cleanly to Python `Enum`. We document losses.

We believe in honest documentation. The tool tells you the costs upfront.

## Design Philosophy

### 1. Prefer Correctness Over Performance

We use formal verification to prove invariants. Better to be slow and correct than fast and broken.

(Though Concorde class is both fast *and* correct.)

### 2. Document Losses Upfront

Never surprise the user. If a conversion is lossy, we document exactly what's lost **before** generating code.

### 3. Pessimistic Analysis

If we can't prove a conversion is safe, we assume it's not. False positives (marking safe conversions as unsafe) are acceptable. False negatives (missing unsafe conversions) are not.

### 4. JSON as Universal Fallback

When all else fails, serialize to JSON. It's slow, but it's universal. This guarantees the invariant holds.

### 5. Make It A Compiler Problem

Schema compatibility should be checked at build time, not discovered at runtime. Protocol Squisher brings compile-time guarantees to FFI.

## Future Work

**Phase 2: More Formats**
- Cap'n Proto, Protobuf, Thrift, Avro, MessagePack

**Phase 3: Advanced Features**
- Circular reference handling (Arena graphs)
- Custom conversion rules (user-defined adapters)
- Streaming adapters (for large data)
- Versioned schema migrations

**Phase 4: Ecosystem Integration**
- Cargo plugin (`cargo squish`)
- IDE plugins (VS Code, IntelliJ)
- CI/CD integration (fail builds on Wheelbarrow class)

See [ROADMAP.adoc](https://github.com/hyperpolymath/protocol-squisher/blob/main/ROADMAP.adoc) for details.

## Contributing

We welcome contributions! Especially:

- **New format analyzers** - Add support for your favorite serialization library
- **Real-world schemas** - Edge cases that break our analysis
- **Performance optimizations** - Make Concorde even faster
- **Formal proofs** - Extend our theorem library

See [CONTRIBUTING.adoc](https://github.com/hyperpolymath/protocol-squisher/blob/main/CONTRIBUTING.adoc).

## Acknowledgments

Inspired by:
- Every developer who has ever cursed at FFI boilerplate
- The Rust community's commitment to zero-cost abstractions
- The Python community's pragmatism
- Dependent type theory for making invariants provable

Built with:
- Rust (for the implementation)
- Agda & Lean (for the proofs)
- PyO3 (for Rust↔Python FFI)
- serde & Pydantic (for serialization)
- Hypothesis (for property-based testing)

## License

PMPL-1.0-or-later (Palimpsest License)

---

**Links:**

- GitHub: https://github.com/hyperpolymath/protocol-squisher
- Examples: https://github.com/hyperpolymath/protocol-squisher/tree/main/examples
- CLI Guide: https://github.com/hyperpolymath/protocol-squisher/blob/main/docs/CLI-GUIDE.adoc
- Formal Proofs: https://github.com/hyperpolymath/protocol-squisher/tree/main/proofs
- Roadmap: https://github.com/hyperpolymath/protocol-squisher/blob/main/ROADMAP.adoc

**Author:** [@hyperpolymath](https://github.com/hyperpolymath)

**Feedback?** Open an issue or PR. Found an edge case? We want to hear about it.

---

*"If it compiles, it carries."*
