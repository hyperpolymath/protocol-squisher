<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell -->

# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

- **Security bridge**: WireGuard tunnel mapping, Noise→TLS reverse requirements,
  NK/KK noise patterns, `BridgeError` type, `SecurityRequirements` struct (+6 tests)
- **Distributed squishing**: `BatchConfig`, `BatchSummary`, `ClassCounts`,
  partitioned execution, per-task timing, `DistributedError` type (+5 tests)
- **Performance/SIMD**: lane-parallel `count_differences`, `bytes_equal`, FNV-1a
  `fast_hash` (+10 tests)
- **Benchmark baseline**: 73 criterion benchmarks across 4 suites captured in
  `benches/BASELINE-v1.0.0.json`
- **RSR workflows**: mirror.yml (6-forge), instant-sync.yml, guix-nix-policy.yml,
  rsr-antipattern.yml, npm-bun-blocker.yml

### Fixed

- Replaced 2 postulates in `WheelbarrowNecessity.agda` with constructive proofs
  (counterexample construction for `narrowing-not-lossless`, case analysis for
  `wheelbarrow-lossy`)
- Filled `{!!}` hole in `CarriesInvariant.agda` adapter-composition proof with
  simultaneous with-matching
- Synchronized all non-Cargo version files to 1.0.0 (Justfile, ipkg, mix.exs,
  lakefile.lean)
- Fixed author email in Idris2 ipkg files (`j.d.a.jewell@open.ac.uk`)
- Fixed SPDX header in root Justfile (`PMPL-1.0` → `PMPL-1.0-or-later`)

### Changed

- Test count: 721 → 742 (21 new tests in Phase 3 scaffolds)
- Security bridge completion: 30% → 60%
- Performance module completion: 20% → 30%
- Distributed module completion: 20% → 30%

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
- **Property-based testing**: 742 tests across all crates
- **Formal verification**: Concorde Safety and Container Propagation theorems fully proven
  in Agda; Concorde Safety cross-validated in Lean
- **Diversity spectrum meta-analysis**: squishability rankings across all 11 protocols
- **Benchmark suite**: transport class overhead validation with Criterion
- **miniKanren adapter synthesis**: constraint-based search for optimal adapters
- **Enterprise scaffolding**: schema registry, version migration, audit logging, governance
- **Security bridge**: TLS/Noise/WireGuard protocol family translation with property verification
- **Distributed squishing**: rayon-based parallel scheduler with batch config and partitioning
- **Performance primitives**: zero-copy paths, lazy deserialization, streaming, byte comparison

### Known Limitations

- Coq, Isabelle, and Z3 proofs are planned but not started
- JSON serialization axioms in CarriesInvariant.agda are postulated (justified runtime assumption)
- Security bridge, enterprise features, and distributed squishing are functional scaffolds
  but not production-hardened
- IDE plugins, web playground, and adapter marketplace do not exist yet

## [0.1.0] - 2025-12-01

### Added

- Initial implementation with Rust and Python analyzers
- Core IR design and type system
- Compatibility engine with transport class scoring
- JSON fallback path
- Basic CLI tool
- Property-based tests
