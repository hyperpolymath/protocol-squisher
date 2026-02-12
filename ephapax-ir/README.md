# protocol-squisher-transport-primitives

Primitive type transport class analysis for protocol-squisher.

## Purpose

This crate classifies conversions between primitive types into transport classes,
providing the foundation for protocol-squisher's compatibility analysis. The
classification is based on ephapax's linear type theory and will eventually be
backed by Idris2 dependent type proofs via FFI.

## Transport Classes

| Class | Overhead | Fidelity | Use Case |
|-------|----------|----------|----------|
| Concorde | 0% | 100% | Exact type match, zero-copy |
| Business | ~5% | 98% | Safe widening (i32->i64) |
| Economy | ~25% | 80% | Container conversion |
| Wheelbarrow | ~80% | 50% | JSON fallback |

## Key Types

- `PrimitiveType` - All primitive IR types (I8-U128, F32, F64, Bool, Char, String, Unit)
- `ContainerType` - Container shapes (Array, Vec, Map, Set, Optional)
- `CompositeType` - Composite shapes (Struct, Enum, Tuple)
- `TransportClass` - The four-tier classification
- `IRContext` - Entry point for compatibility analysis

## Usage

```rust
use protocol_squisher_transport_primitives::{IRContext, PrimitiveType, TransportClass};

let ctx = IRContext::new();
let class = ctx.analyze_compatibility(PrimitiveType::I32, PrimitiveType::I64);
assert_eq!(class, TransportClass::Business);
assert_eq!(class.fidelity(), 98);
assert_eq!(class.overhead(), 5);
```

## The Invariant

**"If it compiles, it carries AND cannot crash"**

Proven by:
1. Idris2's totality checker (all cases handled)
2. Dependent types (types encode proofs)
3. Linear types (resource safety)

## Idris2 Backend

The `idris2/` directory contains the Idris2 implementation with dependent type
proofs. Currently the Rust crate uses pure Rust stubs matching the Idris2
semantics. Once the Idris2 refc-generated C library is available, `src/ffi.rs`
will link to it directly.

## Relationship to ephapax

The ephapax language and compiler live in their own repository. This crate
consumes ephapax's type-theoretic guarantees for protocol conversion safety.
The ephapax compiler is **not** embedded here — it is an external dependency.

## See Also

- [ephapax repo](https://github.com/hyperpolymath/ephapax) - The ephapax language
- [EPHAPAX-INTEGRATION.adoc](../EPHAPAX-INTEGRATION.adoc) - Integration architecture
