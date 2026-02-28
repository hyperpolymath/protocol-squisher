<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell -->

# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

- **GraphQL analyzer** (`protocol-squisher-graphql-analyzer`): SDL parser with type/enum/union/input/
  interface/scalar support, transport compatibility bridge (+15 tests)
- **TOML analyzer** (`protocol-squisher-toml-analyzer`): structural type inference from TOML documents,
  nested tables, array of tables, transport compatibility bridge (+13 tests)
- **Security bridge hardening**: `NegotiationResult`, `SecurityAuditEntry` (JSONL), `ProtocolCapabilities`
  trait, `validate_security_requirements()`, `downgrade_risk()`, `negotiate()` (+10 tests)
- **Enterprise hardening**: `AuditQuery`/`AuditStats`, `PolicyViolation`/`PolicyReport`,
  `MigrationRisk`/`RollbackPlan`, registry `search()`/`list_versions()`, marketplace
  `validate_listing()`/`popularity_score()` (+16 tests)
- **Distributed hardening**: `JobQueue` (priority queue), `ProgressTracker` (atomic counters),
  `RetryPolicy` with backoff, `run_batch_with_retry()`, `DistributedStats` (+7 tests)
- **Performance hardening**: SIMD `find_byte()`/`sum_u32()`/`xor_bytes()`, `ChunkedProcessor`
  with `StreamStats`, `HardwareProfile` detection, `LazySchema` deferred parsing (+12 tests)
- **Coq proofs**: `ConcordeSafety.v` (concorde_preserves_size, concorde_idempotent, concorde_safe),
  `CarriesInvariant.v` (every_pair_classified, transport_class_total, no_economy_for_primitives)
- **Isabelle proofs**: `WheelbarrowNecessity.thy` (wheelbarrow_for_incompatible, narrowing_is_wheelbarrow)
- **Z3/SMT proofs**: transport class exhaustiveness verification, Concorde constraint checking
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

- Test count: 742 → 829 (87 new tests across Phase 3 modules and new analyzers)
- Protocol analyzers: 11 → 13 (added GraphQL and TOML)
- Security bridge completion: 60% → 80%
- Enterprise features completion: 30% → 60%
- Performance module completion: 30% → 50%
- Distributed module completion: 30% → 60%
- Formal proofs: Agda+Lean → Agda+Lean+Coq+Isabelle+Z3 (5 proof systems)

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
- **Property-based testing**: 829 tests across all crates
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

- Coq, Isabelle, and Z3 proofs are initial (not yet verified with actual provers)
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
