# Protocol-Squisher: unwrap() Removal Progress Tracker

> **Started:** 2026-03-30
> **Completed:** 2026-04-03
> **Goal:** Replace all ~932 `.unwrap()` calls with proper error handling
> **Strategy:** Production code -> `?` / `map_err` / custom errors. Tests -> `expect("message")`.
> **Traversal:** Depth-first by crate, highest-count production code first.

## Error Handling Conventions

- All analyzer crates already have `AnalyzerError` (thiserror-derived)
- CLI uses `anyhow`
- VeriSimDB has dedicated `error.rs` with `VeriSimError`
- IR crate has `SchemaError` (manual Display, no thiserror)
- Tests: `.unwrap()` -> `.expect("descriptive message")`
- Production: `.unwrap()` -> `?` operator or `.map_err(...)` as needed

## Crate Status

### TIER 1 -- High-count production crates (30+ unwrap)

| # | Crate | Files | unwrap() | Status | Notes |
|---|-------|-------|----------|--------|-------|
| 1 | messagepack-analyzer | converter(22) parser(20) ephapax_bridge(10) lib(6) | 58 | **DONE** | All test code->expect(). 2 in doc comments left (standard). Compiles clean. |
| 2 | rescript-analyzer | tests/interop(33) ephapax_bridge(15) converter(14) examples(8) lib(6) parser(5) | 81 | **DONE** | All test/example code->expect(). 0 production unwraps. Committed+pushed. |
| 3 | shape-ir | tests(20) benches(1) | 21 | **DONE** | All test+bench code->expect(). 0 production unwraps. Compiles clean. |
| 4 | flatbuffers-analyzer | ephapax_bridge(15) converter(11) parser(8) lib(7) | 41 | **DONE** | Committed+pushed. |
| 5 | avro-analyzer | converter(18) ephapax_bridge(13) parser(5) lib(4) | 40 | **DONE** | Committed+pushed. |
| 6 | protobuf-analyzer | lib(18) ephapax_bridge(13) parser(7) | 38 | **DONE** | Committed+pushed. |
| 7 | capnproto-analyzer | converter(11) parser(10) ephapax_bridge(10) lib(6) | 37 | **DONE** | All test code->expect(). Committed+pushed. |
| 8 | thrift-analyzer | converter(16) ephapax_bridge(13) lib(6) | 35 | **DONE** | All test code->expect(). Committed+pushed. |
| 9 | rust-analyzer | converter(12) ephapax_bridge(9) lib(6) parser(3) attr(1) | 31 | **DONE** | All test code->expect(). Committed+pushed. |

### TIER 2 -- Medium-count crates (15-29 unwrap)

| # | Crate | Files | unwrap() | Status | Notes |
|---|-------|-------|----------|--------|-------|
| 10 | json-schema-analyzer | converter(14) types(10) lib(3) parser(2) | 29 | **DONE** | All test code->expect(). |
| 11 | bebop-analyzer | ephapax_bridge(12) converter(11) lib(6) | 29 | **DONE** | All test code->expect(). |
| 12 | graphql-analyzer | lib(14) parser(7) ephapax_bridge(4) | 25 | **DONE** | 7 production Regex::new->expect("valid static regex"). Rest test code. |
| 13 | sql-analyzer | parser(10) lib(8) converter(4) ephapax_bridge(3) | 25 | **DONE** | All test code->expect(). |
| 14 | integration-tests | lib(24) | 24 | **DONE** | All test code->expect(). |
| 15 | toml-analyzer | lib(17) parser(3) ephapax_bridge(3) | 23 | **DONE** | All test code->expect(). |
| 16 | python-analyzer | ephapax_bridge(11) types(4) lib(4) converter(4) | 23 | **DONE** | All test code->expect(). |
| 17 | constraints | lib(22) | 22 | **DONE** | All test code->expect(). |
| 18 | server | lib(19) | 19 | **DONE** | All test code->expect(). |
| 19 | openapi-analyzer | lib(12) ephapax_bridge(3) parser(2) converter(2) | 19 | **DONE** | All test code->expect(). |
| 20 | arrow-analyzer | lib(11) ephapax_bridge(3) parser(2) converter(1) | 17 | **DONE** | All test code->expect(). |
| 21 | verisimdb | store(13) models(4) | 17 | **DONE** | All test code->expect(). |

### TIER 3 -- Low-count crates (<15 unwrap)

| # | Crate | Files | unwrap() | Status | Notes |
|---|-------|-------|----------|--------|-------|
| 22 | cli | formats(5) feedback(3) integration(2) shape(1) | 11 | **DONE** | 1 production (shape.rs guarded by len check)->expect(). Rest test code. |
| 23 | benches | 4 files | 9 | **DONE** | Bench code->expect(). (shape-ir bench done separately) |
| 24 | echidna-bridge | types(4) tactic(2) cache(1) | 7 | **DONE** | All test code->expect(). |
| 25 | ir | types(2) lib(2) constraints(2) | 6 | **DONE** | All test code->expect(). |
| 26 | examples | 2 files | 5 | **DONE** | Example code->expect(). |
| 27 | pyo3-codegen | optimized(2) module(1) | 3 | **DONE** | 1 in generated code string (correct to leave). 2 test->expect(). |
| 28 | security-bridge | runtime_verify(3) | 3 | **DONE** | All test code->expect(). |
| 29 | distributed | resilience(1) | 1 | **DONE** | Test code->expect(). |

## Progress Summary

- **Total crates:** 29 (grouped from 35 workspace members)
- **Completed:** 29/29
- **unwrap() removed:** ~690 (399 prior + 21 shape-ir + 291 batch)
- **unwrap() remaining:** 7 (all in doc comments, README.md, USAGE.md, or generated code strings -- NOT actionable)
- **Workspace compiles clean:** Yes (`cargo check` passes)

## Residual unwrap() (NOT bugs)

These 7 instances are intentionally left:
1. `pyo3-codegen/src/optimized_gen.rs:339` -- inside a format string that generates Python FFI code
2. `protobuf-analyzer/README.md:75-76` -- documentation example
3. `protobuf-analyzer/USAGE.md:161-162` -- documentation example
4. `rescript-analyzer/README.md:25,35` -- documentation example

## Session Log

### Session 1 -- 2026-03-30
- Created progress tracker, assessed error handling landscape
- **DONE: messagepack-analyzer** -- 56 unwrap()->expect(). COMMITTED.
- rescript-analyzer src/ done. Session ended (credit limit).

### Session 2 -- 2026-03-30 (continued)
- **DONE: rescript-analyzer** -- finished interop_tests.rs(33) + basic_usage.rs(8). COMMITTED+PUSHED.
- **DONE: capnproto-analyzer** -- 37 test unwraps. Batch sed. COMMITTED+PUSHED.
- **DONE: thrift-analyzer** -- 35 test unwraps. Batch sed. COMMITTED+PUSHED.
- **DONE: rust-analyzer** -- 31 test unwraps. Batch sed. COMMITTED+PUSHED.
- **AGENTS DISPATCHED:** shape-ir, flatbuffers, avro, protobuf (background)
- Key finding: ALL analyzer crates have ZERO production unwrap()s.
- Moving to Tier 2 next.

### Session 3 -- 2026-04-03
- **DONE: shape-ir** -- 21 test/bench unwraps->expect(). Compiles clean. COMMITTED.
- **DONE: ALL remaining 20 crates** -- Batch Python script with contextual expect() messages.
  - 8 production unwraps fixed (7 graphql-analyzer Regex::new, 1 cli shape.rs)
  - 283 test unwraps replaced with contextual expect() messages
  - Full workspace `cargo check` passes clean. COMMITTED.
- **PROJECT COMPLETE.** All 29 crates done. 7 residual unwraps in docs/codegen strings.
