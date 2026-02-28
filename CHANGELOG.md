<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell -->

# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Planned

- Phase 4a: `SchemaAnalyzer` trait unifying all 13 analyzers
- Phase 4b: Public library API (re-export IR, compat, meta-analysis from root crate)
- Phase 4c: Constraint evaluation API (`Constraint::evaluate()` for live data)
- Phase 4d: Bidirectional analysis as first-class top-level API
- Phase 4e: `protocol-squisher-server` crate (axum HTTP/JSON API)

## [1.1.1] - 2026-02-28

### Added

- **ROADMAP.adoc rewrite**: Phases 4-6 documenting PanLL substrate integration,
  ProtocolModule design, and Five-Pillar developer suite convergence
- **Five-Pillar architecture**: Languages, Databases, Protocols, Containers, Quality —
  identified Quality/Observability as the missing fifth pillar
- **Three-pane mapping**: Documented how protocol-squisher concepts map to PanLL's
  Pane-L (Symbolic), Pane-N (Neural), Pane-W (World)

### Changed

- Synchronized all 16 non-Cargo version/metadata files to v1.1.0
  (Justfile, README.adoc, STATE.scm, TOPOLOGY.md, HN-ANNOUNCEMENT.md, METRICS.md,
  ephapax-ir.ipkg, ephapax-ir-ffi.ipkg, lakefile.lean, mix.exs, seambot config.toml,
  AGENTIC.scm, ECOSYSTEM.scm, NEUROSYM.scm, PLAYBOOK.scm, SECURITY-REQUIREMENTS.scm)
- Applied `cargo fmt` across all crates
- Updated critical-next-actions to target Phase 4 work

### Security

- panic-attack suite (assail + assault + abduct + adjudicate): **PASS** verdict
- cargo audit: 0 vulnerabilities / 275 dependencies
- All 921 tests passing, cargo clippy clean

## [1.1.0] - 2026-02-28

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
- **ECHIDNA bridge**: 30-backend cross-prover, CLI-integrated, offline fallback
- **VeriSimDB integration**: analysis persistence, InMemory fallback, CLI-integrated
- **Integration pipeline**: `integration.rs` facade wiring ECHIDNA + VeriSimDB into CLI commands
- **Coq proofs**: `ConcordeSafety.v`, `CarriesInvariant.v`
- **Isabelle proofs**: `WheelbarrowNecessity.thy`
- **Z3/SMT proofs**: transport class exhaustiveness verification, Concorde constraint checking
- **Agda proofs**: OptimizationSoundness, extended CarriesInvariant and WheelbarrowNecessity
- **Benchmark baseline**: 73 criterion benchmarks across 4 suites
- **RSR workflows**: mirror.yml (6-forge), instant-sync.yml, guix-nix-policy.yml,
  rsr-antipattern.yml, npm-bun-blocker.yml

### Fixed

- Replaced 2 postulates in `WheelbarrowNecessity.agda` with constructive proofs
- Filled `{!!}` hole in `CarriesInvariant.agda` with simultaneous with-matching
- Synchronized all non-Cargo version files to 1.0.0
- Fixed author email in Idris2 ipkg files
- Fixed SPDX header in root Justfile

### Changed

- Test count: 742 → 921 (179 new tests)
- Protocol analyzers: 11 → 13 (added GraphQL and TOML)
- Formal proofs: Agda+Lean → Agda+Lean+Coq+Isabelle+Z3 (5 proof systems)
- All Phase 3 modules hardened from scaffolds to functional implementations

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
