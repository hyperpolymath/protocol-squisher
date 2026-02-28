---
title: Progress & Contact
slug: progress
order: 4
date: 2026-02-28
tags: [progress, contact, roadmap]
---

# Progress & Contact

## Current Status

protocol-squisher is at **version 1.2.0** with Phases 0 through 4b complete.

### Completed

- **Phase 0: Foundation** — Core IR, constraint system, type mappings
- **Phase 1: MVP** — Rust and Python analysers, transport class system, Agda proofs, CLI
- **Phase 2: Format Expansion** — All 13 analysers implemented and tested, diversity analysis, squishability ranking, hypothesis testing, compatibility matrix
- **Phase 3: Hardening** — Security bridge (negotiation, audit, downgrade risk detection), distributed squishing (job queue, progress, retry), performance primitives (SIMD, chunked streaming, hardware detection, lazy schemas), enterprise features (audit queries, governance, migration validation), cross-validation in Coq, Lean 4, Isabelle, and Z3
- **Phase 4a: SchemaAnalyzer Trait** — Universal trait defined and implemented across all 13 analysers
- **Phase 4b: Public Library API** — Full Rust library API exposed with analyser registry

### In Progress

- **Phase 4c: Constraint Evaluation API** — Making constraints evaluable at runtime, not just declarative
- **Phase 4d: Bidirectional API** — First-class bidirectional comparison
- **Phase 4e: HTTP Server** — `protocol-squisher-server` crate with axum-based REST API

### Planned

- **Phase 5: PanLL Integration** — protocol-squisher as a module in PanLL (neurosymbolic IDE), three-pane protocol analysis
- **Phase 6: Developer Suite Convergence** — Cross-pillar analysis connecting protocols, databases, containers, and quality tools

## Numbers

- **937** automated tests
- **13** protocol format analysers
- **5** formal proof systems (Agda, Coq, Lean 4, Isabelle, Z3)
- **50+** constraint types in the IR
- **4** transport classes (Concorde, Business, Economy, Wheelbarrow)
- **275** cargo dependencies, **0** known vulnerabilities
- **0** clippy warnings

## Timeline

| Date | Milestone |
|------|-----------|
| 2025 Q3 | Project inception, ephapax IR design |
| 2025 Q4 | Phase 1 MVP: Rust/Python, Agda proofs, CLI |
| 2026 Jan | Phase 2: 13 analysers, meta-analysis |
| 2026 Feb | Phase 3: Hardening, cross-proofs, security |
| 2026 Feb 28 | Phase 4a/b: SchemaAnalyzer trait, public API |

## Get in Touch

### For Media and Press

Jonathan D.A. Jewell is available for interviews, conference talks, and technical discussions about protocol interoperability, formal verification in practice, and the future of developer tooling.

- **Email:** j.d.a.jewell@open.ac.uk
- **GitHub:** github.com/hyperpolymath

### For Users and Contributors

- **Issue tracker:** github.com/hyperpolymath/protocol-squisher/issues
- **Discussions:** github.com/hyperpolymath/protocol-squisher/discussions
- **Source code:** github.com/hyperpolymath/protocol-squisher

### For Researchers

If you are working on type theory, serialisation, or formal methods and would like to collaborate, please reach out. The formal proofs in this project are designed to be independently verifiable and we welcome peer review.

## Contributing

protocol-squisher welcomes contributions of all kinds:

- **Bug reports** with reproduction steps
- **New analyser implementations** for additional protocols
- **Proof contributions** in any of the five supported proof systems
- **Documentation improvements** and tutorial writing
- **Performance benchmarks** and optimisation work

See `CONTRIBUTING.md` in the repository for detailed guidelines.

All contributions are released under the Palimpsest License (PMPL-1.0-or-later) unless otherwise specified.
