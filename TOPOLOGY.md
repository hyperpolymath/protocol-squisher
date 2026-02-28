<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
<!-- TOPOLOGY.md — Project architecture map and completion dashboard -->
<!-- Last updated: 2026-02-28 -->

# Protocol Squisher — Project Topology

## System Architecture

```
                        ┌─────────────────────────────────────────┐
                        │              POLYGLOT DEVELOPER         │
                        │        (CLI, Adapter Generation)        │
                        └───────────────────┬─────────────────────┘
                                            │ Format A + Format B
                                            ▼
                        ┌─────────────────────────────────────────┐
                        │           PROTOCOL SQUISHER CORE        │
                        │    (Rust, Analysis & Synthesis)         │
                        └──────────┬───────────────────┬──────────┘
                                   │                   │
                                   ▼                   ▼
                        ┌───────────────────────┐  ┌────────────────────────────────┐
                        │ ANALYZERS (13)        │  │ SYNTHESIS ENGINE               │
                        │ - Protobuf, Avro      │  │ - Canonical IR                 │
                        │ - Cap'n Proto, Thrift │  │ - Compatibility Analysis       │
                        │ - Bebop, FlatBuffers  │  │ - Transport Class Scoring      │
                        │ - GraphQL, TOML       │  │ - ECHIDNA Trust Verification   │
                        └──────────┬────────────┘  └──────────┬─────────────────────┘
                                   │                          │
                                   └────────────┬─────────────┘
                                                ▼
                        ┌─────────────────────────────────────────┐
                        │           GENERATED ADAPTER             │
                        │  ┌───────────┐  ┌───────────────────┐  │
                        │  │ Rust Code │  │  Python Stubs     │  │
                        │  │ (WASM/NIF)│  │  (Pydantic)       │  │
                        │  └───────────┘  └───────────────────┘  │
                        └───────────────────┬─────────────────────┘
                                            │
                                            ▼
                        ┌─────────────────────────────────────────┐
                        │          UNIVERSAL TRANSPORT            │
                        │      (Concorde, Business, Wheelbarrow)  │
                        └─────────────────────────────────────────┘

                        ┌─────────────────────────────────────────┐
                        │     EXTERNAL INTEGRATION (Optional)     │
                        │  ECHIDNA Bridge ──► VeriSimDB Store     │
                        │       │                    │            │
                        │       ▼                    ▼            │
                        │  Cross-Prover       Analysis History    │
                        │  Verification       + Feedback-o-Tron   │
                        └─────────────────────────────────────────┘

                        ┌─────────────────────────────────────────┐
                        │          REPO INFRASTRUCTURE            │
                        │  Justfile Automation  .machines_readable/ │
                        │  Formal Proofs (5 provers) AI.a2ml          │
                        └─────────────────────────────────────────┘
```

## Completion Dashboard

```
COMPONENT                          STATUS              NOTES
─────────────────────────────────  ──────────────────  ─────────────────────────────────
CORE ENGINE
  13 Protocol Analyzers             ██████████ 100%    Bebop to TOML active
  Canonical IR                      ██████████ 100%    Universal mapping stable
  Synthesis Engine                  ██████████ 100%    Minimum viable adapter active
  Transport Class Scoring           ██████████ 100%    Fidelity/Overhead verified

PROOF & VERIFICATION
  Formal Proofs (Agda/Lean/Coq/Isa) ██████████ 100%    8 Agda + Coq/Lean/Isabelle/Z3 cross-validation
  Diversity Analysis                ██████████ 100%    Squishability rankings verified
  Property-Based Tests              ██████████ 100%    937 tests passing

ADVANCED FEATURES (Phase 3+)
  Security Bridge                   █████████░  95%    Negotiation, audit, downgrade, cert expiry, TLS probe
  Enterprise Features               █████████░  95%    Audit, governance, migration, VeriSimDB-backed registry
  Performance (SIMD/streaming)      ██████████ 100%    Byte search, chunked streaming, hardware detect, lazy
  Distributed Squishing             █████████░  90%    Job queue, progress, retry, stats, partition rebalancer

EXTERNAL INTEGRATION (Optional)
  ECHIDNA Bridge                    ██████████ 100%    30-backend cross-prover, CLI-wired, offline fallback
  VeriSimDB Store                   ██████████ 100%    Analysis persistence, InMemory fallback
  Feedback-o-Tron                   ████████░░  80%    Suggestion generation from stored analysis records

REPO INFRASTRUCTURE
  Justfile Automation               ██████████ 100%    Standard build/check tasks
  .machines_readable/6scm           ██████████ 100%    STATE/META/PLAYBOOK tracking active
  Benchmark Suite                   ██████████ 100%    Results interpretation verified

─────────────────────────────────────────────────────────────────────────────
LIBRARY API (Phase 4a/4b)
  SchemaAnalyzer Trait               ██████████ 100%    Implemented across all 13 analyzers
  Public Library API                 ██████████ 100%    prelude, all_analyzers(), 13 re-exported modules
  Constraint Evaluation API          ░░░░░░░░░░   0%    Phase 4c — planned
  protocol-squisher-server           ░░░░░░░░░░   0%    Phase 4e — planned

─────────────────────────────────────────────────────────────────────────────
OVERALL (Phase 1-2):                ██████████ 100%    Core engine + proofs complete
OVERALL (Phase 3):                  █████████░  95%    Hardened + integrated
OVERALL (Phase 4):                  ████░░░░░░  40%    Library extraction started
```

## Key Dependencies

```
Format Analyzers ──► Canonical IR ───► Synthesis Logic ──► Generated Adapter
     │                 │                   │                    │
     ▼                 ▼                   ▼                    ▼
Diversity Spec ───► Compatibility ───► Transport Class ───► Proven Transport
```

## Update Protocol

This file is maintained by both humans and AI agents. When updating:

1. **After completing a component**: Change its bar and percentage
2. **After adding a component**: Add a new row in the appropriate section
3. **After architectural changes**: Update the ASCII diagram
4. **Date**: Update the `Last updated` comment at the top of this file

Progress bars use: `█` (filled) and `░` (empty), 10 characters wide.
Percentages: 0%, 10%, 20%, ... 100% (in 10% increments).
