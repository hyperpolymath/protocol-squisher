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
                        │  Formal Proofs (Agda) AI.a2ml             │
                        └─────────────────────────────────────────┘
```

## Completion Dashboard

```
COMPONENT                          STATUS              NOTES
─────────────────────────────────  ──────────────────  ─────────────────────────────────
CORE ENGINE
  11 Protocol Analyzers             ██████████ 100%    Bebop to ReScript active
  Canonical IR                      ██████████ 100%    Universal mapping stable
  Synthesis Engine                  ██████████ 100%    Minimum viable adapter active
  Transport Class Scoring           ██████████ 100%    Fidelity/Overhead verified

PROOF & VERIFICATION
  Formal Proofs (Agda/Lean)         ██████░░░░  60%    2 verified, 2 partial, 1 planned
  Diversity Analysis                ██████████ 100%    Squishability rankings verified
  Property-Based Tests              ██████████ 100%    721 tests passing

ADVANCED FEATURES (Phase 3+)
  Security Bridge                   ███░░░░░░░  30%    Type scaffolding only
  Enterprise Features               ███░░░░░░░  30%    Scaffolded, not production
  Performance (SIMD/streaming)      ██░░░░░░░░  20%    Zero-copy works; SIMD stub only
  Distributed Squishing             ██░░░░░░░░  20%    Rayon scheduler scaffolded

REPO INFRASTRUCTURE
  Justfile Automation               ██████████ 100%    Standard build/check tasks
  .machines_readable/6scm           ██████████ 100%    STATE/META/PLAYBOOK tracking active
  Benchmark Suite                   ██████████ 100%    Results interpretation verified

─────────────────────────────────────────────────────────────────────────────
OVERALL (Phase 1-2):                █████████░  90%    Core engine complete, proofs partial
OVERALL (Phase 3-4):                ███░░░░░░░  30%    Scaffolded, not production
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
