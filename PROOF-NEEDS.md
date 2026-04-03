# PROOF-NEEDS.md — protocol-squisher

## Current State

- **src/abi/*.idr**: YES — `Types.idr`, `Layout.idr`, `Foreign.idr`
- **Dangerous patterns**: 0 in all proof and ABI code (postulate in CarriesInvariant.agda replaced 2026-04-03 with constructive JSON model)
- **LOC**: ~87,800 (Rust)
- **Existing proofs**: Agda proofs in `proofs/agda/OptimizationSoundness.agda`, Coq proofs in `proofs/coq/ContainerPropagation.v`
- **ABI layer**: Complete Idris2 ABI; 758 `unwrap()` calls in Rust

## What Needs Proving

| Component | What | Why |
|-----------|------|-----|
| IR type constraints | Constraint system is sound and complete | IR is the core representation — constraint bugs affect all formats |
| Optimization soundness | Extend Agda proof beyond current coverage | Optimization must preserve semantics |
| Container propagation | Extend Coq proof coverage | Container type propagation affects serialization correctness |
| Ephapax bridge correctness | All 4 ephapax bridges (Python, Rust, Protobuf, Avro, Cap'n Proto, Thrift) faithfully translate | Incorrect translation produces wrong protocol definitions |
| JSON fallback correctness | Fallback path produces equivalent output | Silent data loss in fallback path |
| PyO3 codegen | Generated Python bindings are correct | Wrong bindings cause runtime crashes in Python consumers |
| Analyzer correctness | All 6 analyzers (Python, Rust, JSON Schema, Protobuf, Avro, Thrift, Cap'n Proto, ReScript) correctly parse their formats | Incorrect parsing produces wrong IR |

## Recommended Prover

**Agda** for optimization soundness (existing). **Coq** for container propagation (existing). **Idris2** for ABI extensions. The 758 `unwrap()` calls are a major safety debt that formal error handling types would address.

## Priority

**HIGH** — Protocol squisher handles serialization format translation. Incorrect translation silently produces wrong data. The existing proof infrastructure (Agda + Coq) demonstrates proof feasibility. The 758 unwrap() calls are the largest safety debt in this scan.
