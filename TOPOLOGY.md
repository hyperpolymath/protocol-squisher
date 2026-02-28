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
                        │ ANALYZERS (11+)       │  │ SYNTHESIS ENGINE               │
                        │ - Protobuf, Avro      │  │ - Canonical IR                 │
                        │ - Cap'n Proto, Thrift │  │ - Compatibility Analysis       │
                        │ - Bebop, FlatBuffers  │  │ - Transport Class Scoring      │
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
  Formal Proofs (Agda/Lean/Coq/Isa) ██████████ 100%    5 Agda + Coq/Isabelle/Z3 cross-validation
  Diversity Analysis                ██████████ 100%    Squishability rankings verified
  Property-Based Tests              ██████████ 100%    829 tests passing

ADVANCED FEATURES (Phase 3+)
  Security Bridge                   ████████░░  80%    Negotiation, audit, downgrade risk, capabilities
  Enterprise Features               ██████░░░░  60%    Audit queries, governance reports, migration validation
  Performance (SIMD/streaming)      █████░░░░░  50%    Byte search, chunked streaming, hardware detect, lazy
  Distributed Squishing             ██████░░░░  60%    Job queue, progress tracking, retry policies, stats

REPO INFRASTRUCTURE
  Justfile Automation               ██████████ 100%    Standard build/check tasks
  .machines_readable/6scm           ██████████ 100%    STATE/META/PLAYBOOK tracking active
  Benchmark Suite                   ██████████ 100%    Results interpretation verified

─────────────────────────────────────────────────────────────────────────────
OVERALL (Phase 1-2):                ██████████ 100%    Core engine + proofs complete
OVERALL (Phase 3-4):                ██████░░░░  60%    Hardened scaffolds, approaching production
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
