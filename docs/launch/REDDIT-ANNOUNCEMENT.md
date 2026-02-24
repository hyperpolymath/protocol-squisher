# I built a tool that auto-generates adapters between any two serialization formats (Rust↔Python working, 678 tests, formally verified)

Hey everyone,

I've been working on solving a problem that's bugged me for years: the tedious, error-prone work of writing adapters between different serialization formats.

## The Pain Point

You know the drill. You have a Rust service using serde, your coworker has a Python service with Pydantic models, and you need them to talk. So you:

1. Write 200+ lines of PyO3 boilerplate
2. Debug segfaults for a day
3. Maintain it forever as schemas drift
4. Repeat for every service boundary

I got tired of this and built **Protocol Squisher**.

## What It Does

Give it two schemas (say, Rust types and Python Pydantic models), and it:

1. **Analyzes compatibility** - Tells you upfront if transport is possible and at what cost
2. **Generates adapters** - Creates PyO3 bindings, type stubs, tests automatically
3. **Optimizes for zero-copy** - When types match perfectly, you get direct memory access
4. **Proves correctness** - Formal verification in Agda/Lean that the adapter is safe

## Show Me Code

**Before (manual):**
```python
# 50+ lines of PyO3 boilerplate per struct
# Manual type conversions
# No safety guarantees
# Segfaults waiting to happen
```

**After:**
```bash
$ protocol-squisher check --rust lib.rs --python models.py

Transport Class: Concorde (100% fidelity, 0% overhead)
  ✓ user_id: i64 ↔ int (native)
  ✓ balance: f64 ↔ float (IEEE 754)
  ✓ name: String ↔ str (UTF-8)

$ protocol-squisher generate --rust lib.rs --python models.py

Generated:
  ✓ PyO3 bindings (657 lines)
  ✓ Type stubs (.pyi)
  ✓ Property-based tests
```

**Result:** ~1 nanosecond per field access. Zero-copy between Rust and Python.

## Real Performance Numbers

I benchmarked the `zero-copy-demo` example:

| Transport Class | Field Access | Notes |
|-----------------|--------------|-------|
| **Concorde** | ~1ns | Direct memory, no conversion |
| **Business** | ~2-5ns | Safe widening (i32→i64) |
| **Economy** | ~10-50ns | Minor conversions |
| **Wheelbarrow** | ~100-1000ns | JSON fallback for narrowing |

## The "If It Compiles, It Carries" Invariant

The core guarantee:

> For any valid input in format A, there exists a valid output in format B.

Even if slow. Even if lossy. But it **will** transport.

This is backed by formal proofs in Agda and Lean (yes, actual theorem prover proofs). See the `/proofs` directory.

## Transport Classes Explained

Every schema pair gets classified:

- **Concorde**: Perfect match (i64↔int). Zero-copy. ~1ns.
- **Business**: Safe conversions (i32→i64). Minor overhead. ~5ns.
- **Economy**: Documented losses. Moderate overhead. ~50ns.
- **Wheelbarrow**: Significant losses (i64→i32). JSON fallback. ~1000ns.

The tool tells you which class you get **before** generating code, so no surprises.

## Example: Rust ↔ Python

**Rust side:**
```rust
#[derive(Serialize, Deserialize)]
struct User {
    user_id: i64,
    balance: f64,
    name: String,
    active: bool,
}
```

**Python side:**
```python
from pydantic import BaseModel

class User(BaseModel):
    user_id: int
    balance: float
    name: str
    active: bool
```

**Analysis:**
```
Transport Class: Concorde
All fields: direct memory mapping
Zero serialization overhead
```

**Generated code handles:**
- PyO3 `#[pyclass]` annotations
- Lifetime management
- Error handling
- Type conversions
- Property-based tests

## Current Status

**MVP Complete:**
- ✅ 678 tests passing
- ✅ Rust ↔ Python fully working
- ✅ All 4 transport classes implemented
- ✅ 4 theorems proven (Agda + Lean)
- ✅ CLI with analyze/check/optimize/generate
- ✅ Comprehensive docs

**Supported formats:**
- Rust (serde), Python (Pydantic), Protobuf, Thrift, Avro, MessagePack, FlatBuffers, Cap'n Proto, Bebop, ReScript, JSON Schema

**Current focus (next):**
- Larger real-world schema corpus
- Synthesis quality improvements
- Advanced FFI hardening + performance tuning

## Try It Yourself

```bash
git clone https://github.com/hyperpolymath/protocol-squisher
cd protocol-squisher/examples/zero-copy-demo
./build.sh
python test.py  # See the magic
```

Or install the CLI:
```bash
cargo install --path crates/protocol-squisher-cli
protocol-squisher --help
```

## Why I Built This

I've wasted **weeks** writing manual FFI adapters across projects. Every time:
- Boilerplate city
- Subtle bugs from manual conversions
- Schemas drift, adapters break
- No way to know if transport is even possible

Protocol Squisher makes this a build-time analysis instead of a runtime surprise.

## Limitations (Being Real)

1. **Wheelbarrow class is slow** - Narrowing conversions (i64→i32) need JSON serialization (100-1000x overhead)
2. **Analysis needs schemas** - No runtime inference yet
3. **Optimization quality differs by pair** - Some conversions still land in Wheelbarrow class until synthesis improves

We don't hide the costs. The tool tells you upfront: "This conversion is Wheelbarrow class, expect 100-1000x overhead."

## Formal Verification

The `/proofs` directory has formal proofs in multiple theorem provers:

- **Agda**: Dependent types, constructive proofs
- **Lean**: Modern prover with great tooling
- **Coq**: Classic, well-established

**Proven theorems:**
1. Concorde class is lossless and bijective
2. Narrowing conversions require fallback
3. Container transport class = worst element class
4. Optimization suggestions preserve semantics

This isn't just "tests pass." These are mathematical proofs.

## What I'm Looking For

**Feedback:**
- Does this solve a real pain point for you?
- What formats would you want next?
- Edge cases that break the analysis?

**Contributions:**
- New format analyzers
- Real-world schemas that break things
- Performance optimizations
- More formal proofs

## Links

- **GitHub**: https://github.com/hyperpolymath/protocol-squisher
- **Examples**: https://github.com/hyperpolymath/protocol-squisher/tree/main/examples
- **CLI Docs**: https://github.com/hyperpolymath/protocol-squisher/blob/main/docs/CLI-GUIDE.adoc
- **Formal Proofs**: https://github.com/hyperpolymath/protocol-squisher/tree/main/proofs

## License

PMPL-1.0-or-later (Palimpsest License)

---

Happy to answer questions, discuss the approach, or hear about edge cases I haven't considered. This is an MVP, and I'm actively looking for ways to break it.

If you've ever spent a day debugging PyO3 boilerplate or cursed at FFI, this might save you some pain.

**Edit:** Added performance numbers, clarified Wheelbarrow class overhead, fixed links.
