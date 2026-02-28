---
title: Technology
slug: technology
order: 3
date: 2026-02-28
tags: [technology, rust, formal-verification, ir]
---

# Technology

protocol-squisher is built on a layered architecture that separates concerns cleanly: analysis at the bottom, comparison in the middle, and synthesis at the top. Every layer is implemented in Rust and backed by formal proofs.

## The Intermediate Representation (IR)

At the core of protocol-squisher is the **ephapax IR** — a format-independent schema representation that captures the full semantics of any serialisation protocol. When an analyser processes a schema file, it produces an `IrSchema` value containing:

- **Fields** with names, types, optionality, and default values
- **Nested structures** preserving the full hierarchy
- **Constraints** — over 50 constraint types covering numeric ranges, string patterns, enum membership, precision bounds, and structural invariants
- **Type mappings** connecting protocol-specific types to normalised IR types
- **Metadata** including field ordering, deprecation status, and documentation

The IR is the universal language that all 13 analysers speak. It is defined in the `protocol-squisher-ir` crate and is the foundation for every subsequent operation.

## The Constraint System

Constraints are the heart of compatibility analysis. Each field in a schema carries zero or more constraints that describe what values are valid. When comparing two schemas, protocol-squisher evaluates how constraints relate to each other:

- **Equivalent** constraints produce Concorde (lossless) transport
- **Subset** constraints produce Business (safe widening) transport
- **Overlapping** constraints produce Economy (lossy but functional) transport
- **Disjoint** constraints produce Wheelbarrow (manual intervention) transport

The constraint system supports range checks, pattern matching, enum membership, nullability, precision bounds, and recursive structural constraints. It is designed to be extensible — new constraint types can be added without breaking existing analyses.

## Transport Classes

Transport classes are protocol-squisher's answer to the question: *how much can we trust this translation?*

**Concorde** is the gold standard. Both schemas represent the same information with the same precision. Translation is a no-op in the best case or a trivial type rename in the worst. Round-tripping is always lossless.

**Business** means the translation is safe in one direction but not perfectly symmetric. For example, widening an `int32` to an `int64` is always safe, but narrowing back might lose data. protocol-squisher generates the forward adapter automatically and warns about the reverse.

**Economy** means information loss is expected but the translation is still useful. A `float64` to `float32` conversion loses precision; a nullable field mapped to a required field loses the null case. protocol-squisher generates the adapter with explicit annotations marking every loss point.

**Wheelbarrow** means the schemas are too different for automatic bridging. A `string` field mapped to a `boolean` field, or an entirely missing required field, cannot be resolved without human decisions. protocol-squisher identifies these cases and generates a stub with TODO markers.

## Meta-Analysis

Beyond individual comparisons, protocol-squisher can analyse the entire landscape of supported protocols through its meta-analysis engine:

- **Diversity analysis** measures how different two protocols are in their design philosophy (schema evolution vs. zero-copy vs. dynamic vs. validation-centric)
- **Squishability ranking** scores each protocol on how amenable it is to translation
- **Hypothesis testing** validates claims like "schema evolution protocols are more interoperable" with actual data across all pairwise comparisons

The meta-analysis confirmed that Avro and Thrift (schema evolution protocols) achieve the highest squishability scores, while Cap'n Proto and FlatBuffers (zero-copy protocols) are already so optimised that translation rarely improves them.

## Performance

protocol-squisher is designed for production use:

- **SIMD byte search** for fast schema scanning on x86_64 and aarch64
- **Chunked streaming** for processing schemas that exceed available memory
- **Hardware detection** at startup to select optimal code paths
- **Lazy schema loading** to avoid parsing unused sections
- **Zero-copy where possible** — the IR reuses schema data without allocation when safe

## ECHIDNA Integration

ECHIDNA is a cross-prover theorem verification bridge that connects 30 proof backends. protocol-squisher uses ECHIDNA to:

- Verify formal proofs across Agda, Coq, Lean 4, Isabelle, and Z3
- Provide offline fallback when cloud provers are unavailable
- Generate proof obligations from compatibility analyses

The integration is available through the CLI and can be used to certify that a specific translation meets formal requirements.

## VeriSimDB Integration

Analysis results can be persisted to VeriSimDB (a verified similarity database) for historical tracking. This enables:

- Trend analysis of compatibility over time as schemas evolve
- Registry of known-good translations for reuse
- Audit trails for compliance-sensitive environments

When VeriSimDB is not available, protocol-squisher falls back to an in-memory store transparently.

## The Rust Ecosystem

protocol-squisher is a pure Rust project with:

- **937 tests** covering unit, integration, property-based, and formal verification tests
- **0 vulnerabilities** in 275 dependencies (verified by cargo audit)
- **clippy clean** with no warnings
- **All stable Rust** — no nightly features required

The codebase compiles on Linux, macOS, and Windows without platform-specific code.
