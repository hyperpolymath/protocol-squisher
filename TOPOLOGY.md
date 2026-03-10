<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
<!-- TOPOLOGY.md — Project architecture map and completion dashboard -->
<!-- Last updated: 2026-03-10f -->

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

## Vision Architecture (18-Month Plan — Phase 1 In Progress)

The existing architecture above remains valid as the **foundation layer**. The
vision adds a new **Shape IR layer** underneath it that generalises the Canonical
IR to reason about all data shapes, not just serialization formats.

```
                    ┌──────────────────────────────────────────────────────┐
                    │            UNIVERSAL DATA SHAPE LAYER               │
                    │               (NEW — Phase 1+)                      │
                    │                                                      │
                    │  ┌────────────────────────────────────────────────┐  │
                    │  │  shape-ir crate (crates/shape-ir/)            │  │
                    │  │  ┌──────────┐ ┌────────────┐ ┌────────────┐  │  │
                    │  │  │  Shape   │ │ Transport  │ │ Linearity  │  │  │
                    │  │  │  enum    │ │ Class      │ │ Lattice    │  │  │
                    │  │  │(11 ctors)│ │ (semilat.) │ │ (4-point)  │  │  │
                    │  │  └──────────┘ └────────────┘ └────────────┘  │  │
                    │  │  ┌──────────────┐  ┌────────────────────┐    │  │
                    │  │  │ Information  │  │ Comparison Engine  │    │  │
                    │  │  │ Content +    │  │ (shape × shape →   │    │  │
                    │  │  │ MorphMetrics │  │  morphism + class) │    │  │
                    │  │  └──────────────┘  └────────────────────┘    │  │
                    │  │  ┌──────────────┐  ┌────────────────────┐    │  │
                    │  │  ┌──────────────┐  ┌────────────────────┐    │  │
                    │  │  │ ShapeCat.   │  │ Adapter Discovery  │    │  │
                    │  │  │ (category   │  │ (Dijkstra minimax  │    │  │
                    │  │  │ +monoidal)  │  │  pathfinding)      │    │  │
                    │  │  └──────────────┘  └────────────────────┘    │  │
                    │  │  ┌──────────────┐  ┌────────────────────┐    │  │
                    │  │  │ Shape Extr.  │  │ CLI Integration    │    │  │
                    │  │  │ (IR→Shape)   │  │ (extract+compare   │    │  │
                    │  │  └──────────────┘  │  +graph)           │    │  │
                    │  │                    └────────────────────┘    │  │
                    │  └────────────────────────────────────────────────┘  │
                    │                         ▲                            │
                    │           ┌──────────────┴──────────────┐            │
                    │           │    Shape Extractors          │            │
                    │           │  (one per domain)            │            │
                    │  ┌────────┴──┐ ┌────────┐ ┌──────────┐  │            │
                    │  │ Protobuf  │ │ SQL DDL│ │ OpenAPI  │  │            │
                    │  │ Avro      │ │ Arrow  │ │ Rust AST │  │            │
                    │  │ ... (13)  │ │        │ │ Zig/C    │  │            │
                    │  └───────────┘ └────────┘ └──────────┘  │            │
                    │  (existing)     (Phase 3)  (Phase 3)    │            │
                    │           └──────────────────────────────┘            │
                    └──────────────────────────────────────────────────────┘
                                          │
                              ┌────────────┴────────────┐
                              ▼                         ▼
                    ┌───────────────────┐     ┌───────────────────┐
                    │  Shape Algebra    │     │  Temporal Algebra │
                    │  (Phase 2)        │     │  (Phase 4)        │
                    │  Category, compos.│     │  Evolution, ver.  │
                    │  Pathfinding      │     │  Forecasting      │
                    └───────────────────┘     └───────────────────┘
                              │                         │
                              └────────────┬────────────┘
                                           ▼
                    ┌──────────────────────────────────────────────────────┐
                    │  Visual & Interface Layer (Phase 5)                 │
                    │  TUI (ratatui) │ PanLL (L/N/W) │ Web               │
                    └──────────────────────────────────────────────────────┘
```

## Completion Dashboard

```
COMPONENT                          STATUS              NOTES
─────────────────────────────────  ──────────────────  ─────────────────────────────────
CORE ENGINE
  17 Protocol Analyzers             ██████████ 100%    13 serialization + SQL DDL + OpenAPI + Arrow IPC + TOML
  Canonical IR                      ██████████ 100%    Universal mapping stable
  Synthesis Engine                  ██████████ 100%    Minimum viable adapter active
  Transport Class Scoring           ██████████ 100%    Fidelity/Overhead verified

PROOF & VERIFICATION
  Formal Proofs (Agda/Lean/Coq/Isa) ██████████ 100%    8 Agda + Coq/Lean/Isabelle/Z3 cross-validation
  Diversity Analysis                ██████████ 100%    Squishability rankings verified
  Property-Based Tests              ██████████ 100%    1378 tests passing

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
VISION: UNIVERSAL DATA SHAPE (18-Month Plan)
  shape-ir crate (Phase 1)         ██████████ 100%    SEALED — 11 ctors, comparison, extraction, metrics, compose (16 tests), extract edge cases
  Shape Algebra (Phase 2)          ██████████ 100%    SEALED — ShapeCategory (laws, Dijkstra, monoidal), 35 unit + property tests
  Domain Extractors (Phase 3)      ██████████ 100%    SEALED — SQL+OpenAPI+Arrow, 22 cross-domain tests, 7-format category test
  Temporal Algebra (Phase 4)       ██████████ 100%    SchemaTimeline, SemverClassification, forecast, evolution strategy, 29 tests
  Visual Language (Phase 5)        ██████████ 100%    SEALED — render.rs + panll.rs + CLI (render/dot/timeline/panll), 12 seam tests, 70 total Phase 5 tests
  Paper + Release (Phase 6)        ░░░░░░░░░░   0%    Not started — months 16-18

─────────────────────────────────────────────────────────────────────────────
LIBRARY API (Phase 4a/4b)
  SchemaAnalyzer Trait               ██████████ 100%    Implemented across all 17 analyzers
  Public Library API                 ██████████ 100%    prelude, all_analyzers(), 13 re-exported modules
  Constraint Evaluation API          ██████████ 100%    5 SchemaConstraint variants, 20+ value Constraints, 27 tests
  protocol-squisher-server           ██████████ 100%    axum, 5 endpoints (health/formats/analyze/compare/constraints), 5 tests

─────────────────────────────────────────────────────────────────────────────
OVERALL (Original Phase 1-2):       ██████████ 100%    Core engine + proofs complete
OVERALL (Original Phase 3):         █████████░  95%    Hardened + integrated
OVERALL (Original Phase 4):         ██████████ 100%    Library API + constraints + server complete
OVERALL (Vision Phase 1):           ██████████ 100%    COMPLETE — 124 tests, full engine
OVERALL (Vision Phase 2):           ██████████ 100%    Phases 1-5 SEALED — 1378 tests, render + panll + CLI visual layer
```

## Key Dependencies

```
Format Analyzers ──► Canonical IR ───► Synthesis Logic ──► Generated Adapter
     │                 │                   │                    │
     ▼                 ▼                   ▼                    ▼
Diversity Spec ───► Compatibility ───► Transport Class ───► Proven Transport

Vision (new):
Shape Extractors ──► shape-ir ──► Shape Algebra ──► Morphisms ──► Visual Layer
  (17 analyzers       (Phase 1     (Phase 2)         (Phase 2)     (Phase 5)
   + SQL + OpenAPI)    SEALED)      SEALED            SEALED        SEALED
```

## Update Protocol

This file is maintained by both humans and AI agents. When updating:

1. **After completing a component**: Change its bar and percentage
2. **After adding a component**: Add a new row in the appropriate section
3. **After architectural changes**: Update the ASCII diagram
4. **Date**: Update the `Last updated` comment at the top of this file

Progress bars use: `█` (filled) and `░` (empty), 10 characters wide.
Percentages: 0%, 10%, 20%, ... 100% (in 10% increments).
