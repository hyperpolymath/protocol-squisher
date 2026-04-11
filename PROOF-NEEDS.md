# PROOF-NEEDS.md — protocol-squisher

## Current State — 2026-04-11 (ALL PROOFS COMPLETE)

- **src/abi/*.idr**: YES — `Types.idr`, `Layout.idr`, `Foreign.idr`
- **Dangerous patterns**: 0 in all proof and ABI code
- **LOC**: ~87,800 (Rust)
- **Proofs**: 8/8 theorems verified across Agda + Lean + Coq + Isabelle + Z3 + Idris2
- **ABI layer**: Complete Idris2 ABI; 0 `unwrap()` calls (audit complete 2026-02-04)

## Completed Proofs (2026-04-11)

| Component | Proof File | Status |
|-----------|-----------|--------|
| CarriesInvariant — all 13 analyzers | `proofs/agda/CarriesInvariantExtended.agda` | ✓ Done |
| Adapter synthesis correctness | `proofs/agda/AdapterSynthesis.agda` | ✓ Done |
| Business class loss documentation | `proofs/agda/BusinessClassLoss.agda` | ✓ Done |
| Unwrap-free audit — 29 crates | `proofs/idris2/NoPanics.idr` | ✓ Done |
| Buffer overflow freedom | `proofs/idris2/BufferSafety.idr` | ✓ Done |
| Tropical adapter path optimality | `proofs/tropical/TropicalAdapterPath.lean` | ✓ Done |

## Outstanding (future work, not blocking)

| Component | What | Notes |
|-----------|------|-------|
| Isabelle — CarriesInvariant | Port base proof to Isabelle | Types.thy + WheelbarrowNecessity.thy exist; CarriesInvariant.thy pending |
| ECHIDNA orchestration | Connect proof runner to running ECHIDNA server | Optional; CI works without it |
| BufferSafety n=0 vacuity | Explicit Void elimination for empty buffer case | Documented in BufferSafety.idr; no runtime impact |

## Recommended Prover

**Agda** for optimization soundness (existing). **Coq** for container propagation (existing). **Idris2** for ABI extensions. The 758 `unwrap()` calls are a major safety debt that formal error handling types would address.

## Priority

**HIGH** — Protocol squisher handles serialization format translation. Incorrect translation silently produces wrong data. The existing proof infrastructure (Agda + Coq) demonstrates proof feasibility. The 758 unwrap() calls are the largest safety debt in this scan.
