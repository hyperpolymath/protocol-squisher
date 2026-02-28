---
title: The Project
slug: project
order: 2
date: 2026-02-28
tags: [project, overview, architecture]
---

# The Project

protocol-squisher is a Rust library and command-line tool that analyses, compares, and bridges serialisation protocols. It works with 13 protocol formats, runs 937 automated tests, and backs its results with formal proofs verified in five independent proof systems.

## What it does

**Analyse** any supported schema to produce a format-independent intermediate representation (IR). The IR captures every field, constraint, nesting relationship, and type mapping in a normalised form that can be compared across protocols.

**Compare** two schemas to produce a detailed compatibility report. The report classifies every field mapping into one of four transport classes:

- **Concorde** — Lossless, bidirectional translation. Both sides carry the same information.
- **Business** — Lossless in one direction; minor precision differences in the reverse.
- **Economy** — Translation is possible but some information is lost (e.g., widening a uint16 to uint32).
- **Wheelbarrow** — Manual intervention required. The schemas are too different for automatic bridging.

**Generate** adapter code that performs the translation. The generated code respects the transport class: Concorde mappings are zero-overhead, Economy mappings carry explicit loss annotations, and Wheelbarrow fields are flagged for human review.

## The 13 analysers

| Format | Protocol Family | Key Characteristics |
|--------|----------------|---------------------|
| Rust | Language-native | Ownership, lifetimes, trait bounds |
| Python | Language-native | Dynamic typing, duck typing conventions |
| JSON Schema | Web/API | Validation-centric, format keywords |
| Protocol Buffers | Google RPC | Field numbers, wire types, proto3 defaults |
| Avro | Data pipeline | Schema evolution, union types |
| FlatBuffers | Zero-copy | In-place access, no parsing |
| Cap'n Proto | Zero-copy | Pointer-based, canonical encoding |
| MessagePack | Binary JSON | Compact, schemaless |
| Thrift | Apache RPC | IDL-driven, multiple transports |
| ReScript | Typed JS | Variant types, pattern matching |
| GraphQL | API query | Selection sets, nullable-by-default |
| TOML | Configuration | Section nesting, typed values |
| Bebop | Game dev | Fixed layouts, performant serialisation |

Each analyser implements the `SchemaAnalyzer` trait, providing a consistent `analyze_file` and `analyze_str` interface. The trait is defined in the `protocol-squisher-ir` crate and enables programmatic access to all 13 analysers through a single registry.

## Architecture

protocol-squisher is structured as a Cargo workspace with modular crates:

- **protocol-squisher** — Root crate, public API, analyser registry
- **protocol-squisher-ir** — Intermediate representation, `SchemaAnalyzer` trait, constraint system (50+ constraint types)
- **protocol-squisher-compat** — Compatibility analysis, transport class assignment, bidirectional comparison
- **protocol-squisher-meta-analysis** — Cross-format diversity analysis, squishability ranking, hypothesis testing
- **13 analyser crates** — One per supported format, each self-contained
- **protocol-squisher-optimizer** — Adapter code optimisation
- **protocol-squisher-codegen** — Code generation for Rust and Python adapters

## The formal guarantee

The core invariant — *if it compiles, it carries* — is not marketing. It is a mathematical theorem proven in five independent formal verification systems:

- **Agda** — 8 theorems covering preservation, composition, and transport class ordering
- **Coq** — ConcordeSafety and CarriesInvariant proofs
- **Lean 4** — Machine-checked verification of the invariant
- **Isabelle/HOL** — WheelbarrowNecessity proof (lower bound on the classification)
- **Z3/SMT** — Exhaustiveness check across all constraint combinations

The proofs live in the repository under `proofs/` and are checked in CI.

## Using it

As a CLI tool:

```
protocol-squisher analyze schema.proto
protocol-squisher compare schema.proto schema.avsc
protocol-squisher squishability schema.json
```

As a Rust library:

```
use protocol_squisher::prelude::*;
use protocol_squisher::all_analyzers;

let analyzers = all_analyzers();
for a in &analyzers {
    println!("{}: {:?}", a.analyzer_name(), a.supported_extensions());
}
```

## License

protocol-squisher is released under the Palimpsest License (PMPL-1.0-or-later), a free and open-source license with no corporate governance requirements.
