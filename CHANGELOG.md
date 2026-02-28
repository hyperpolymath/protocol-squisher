<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell -->

# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [1.0.0] - 2026-02-28

### Added

- **11 protocol analyzers**: Rust, Python, JSON Schema, Protobuf, Bebop, FlatBuffers,
  MessagePack, Avro, Cap'n Proto, Thrift, ReScript
- **Canonical IR** (ephapax): universal intermediate representation with Idris2 dependent
  type foundations
- **Compatibility engine**: automatic transport class scoring (Concorde, Business, Economy,
  Wheelbarrow) for any format pair
- **JSON fallback**: guaranteed Wheelbarrow-class transport for all format pairs
- **PyO3 code generation**: automatic Rust-Python binding generation
- **Optimizer**: Concorde-class adapter suggestions with zero-copy detection
- **CLI tool** (`protocol-squisher`): subcommands for `analyze-schema`, `check`, `optimize`,
  `generate`, `optimize-ai`, `diversity-report`, and `synthesize`
- **Property-based testing**: 721 tests across all crates
- **Formal verification**: Concorde Safety and Container Propagation theorems fully proven
  in Agda; Concorde Safety cross-validated in Lean
- **Diversity spectrum meta-analysis**: squishability rankings across all 11 protocols
- **Benchmark suite**: transport class overhead validation with Criterion
- **miniKanren adapter synthesis**: constraint-based search for optimal adapters
- **Enterprise scaffolding**: schema registry, version migration, audit logging, governance
- **Security bridge scaffolding**: TLS/Noise protocol family type definitions
- **Distributed squishing scaffolding**: rayon-based parallel scheduler
- **Performance primitives**: zero-copy paths, lazy deserialization, streaming scaffolding

### Known Limitations

- Formal proofs for Wheelbarrow Necessity (2 postulates) and Carries Invariant (1 hole)
  are partial — see `proofs/README.adoc` for details
- Coq, Isabelle, and Z3 proofs are planned but not started
- Security bridge, enterprise features, and distributed squishing are scaffolded
  but not production-ready
- SIMD acceleration is a stub (`xor_checksum` toy function only)
- IDE plugins, web playground, and adapter marketplace do not exist yet

## [0.1.0] - 2025-12-01

### Added

- Initial implementation with Rust and Python analyzers
- Core IR design and type system
- Compatibility engine with transport class scoring
- JSON fallback path
- Basic CLI tool
- Property-based tests
