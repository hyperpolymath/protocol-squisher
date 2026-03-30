# Protocol-Squisher: unwrap() Removal Progress Tracker

> **Started:** 2026-03-30
> **Goal:** Replace all ~932 `.unwrap()` calls with proper error handling
> **Strategy:** Production code → `?` / `map_err` / custom errors. Tests → `expect("message")`.
> **Traversal:** Depth-first by crate, highest-count production code first.

## Error Handling Conventions

- All analyzer crates already have `AnalyzerError` (thiserror-derived)
- CLI uses `anyhow`
- VeriSimDB has dedicated `error.rs` with `VeriSimError`
- IR crate has `SchemaError` (manual Display, no thiserror)
- Tests: `.unwrap()` → `.expect("descriptive message")`
- Production: `.unwrap()` → `?` operator or `.map_err(...)` as needed

## Crate Status

### TIER 1 — High-count production crates (30+ unwrap)

| # | Crate | Files | unwrap() | Status | Notes |
|---|-------|-------|----------|--------|-------|
| 1 | messagepack-analyzer | converter(22) parser(20) ephapax_bridge(10) lib(6) | 58 | **DONE** | All test code→expect(). 2 in doc comments left (standard). Compiles clean. |
| 2 | rescript-analyzer | tests/interop(33) ephapax_bridge(15) converter(14) examples(8) lib(6) parser(5) | 81 | **IN PROGRESS** | ephapax_bridge.rs DONE, converter.rs DONE, lib.rs DONE, parser.rs DONE. **REMAINING: tests/interop_tests.rs (33) + examples/basic_usage.rs (8) — NOT YET TOUCHED.** Production code had 0 real unwrap()s. |
| 3 | shape-ir | tests(74) category(3) compose(1) benches(1) | 81 | NOT STARTED | 74 in tests |
| 4 | flatbuffers-analyzer | ephapax_bridge(15) converter(11) parser(8) lib(7) | 41 | NOT STARTED | |
| 5 | avro-analyzer | converter(18) ephapax_bridge(13) parser(5) lib(4) | 40 | NOT STARTED | |
| 6 | protobuf-analyzer | lib(18) ephapax_bridge(13) parser(7) | 38 | NOT STARTED | |
| 7 | capnproto-analyzer | converter(11) parser(10) ephapax_bridge(10) lib(6) | 37 | NOT STARTED | |
| 8 | thrift-analyzer | converter(16) ephapax_bridge(13) lib(6) | 35 | NOT STARTED | |
| 9 | rust-analyzer | converter(12) ephapax_bridge(9) lib(6) parser(3) attr(1) | 31 | NOT STARTED | |

### TIER 2 — Medium-count crates (15-29 unwrap)

| # | Crate | Files | unwrap() | Status | Notes |
|---|-------|-------|----------|--------|-------|
| 10 | json-schema-analyzer | converter(14) types(10) lib(3) parser(2) | 29 | NOT STARTED | |
| 11 | bebop-analyzer | ephapax_bridge(12) converter(11) lib(6) | 29 | NOT STARTED | |
| 12 | graphql-analyzer | lib(14) parser(7) ephapax_bridge(4) | 25 | NOT STARTED | |
| 13 | sql-analyzer | parser(10) lib(8) converter(4) ephapax_bridge(3) | 25 | NOT STARTED | |
| 14 | integration-tests | lib(24) | 24 | NOT STARTED | All test code |
| 15 | toml-analyzer | lib(17) parser(3) ephapax_bridge(3) | 23 | NOT STARTED | |
| 16 | python-analyzer | ephapax_bridge(11) types(4) lib(4) converter(4) | 23 | NOT STARTED | |
| 17 | constraints | lib(22) | 22 | NOT STARTED | |
| 18 | server | lib(19) | 19 | NOT STARTED | |
| 19 | openapi-analyzer | lib(12) ephapax_bridge(3) parser(2) converter(2) | 19 | NOT STARTED | |
| 20 | arrow-analyzer | lib(11) ephapax_bridge(3) parser(2) converter(1) | 17 | NOT STARTED | |
| 21 | verisimdb | store(13) models(4) | 17 | NOT STARTED | Has error.rs |

### TIER 3 — Low-count crates (<15 unwrap)

| # | Crate | Files | unwrap() | Status | Notes |
|---|-------|-------|----------|--------|-------|
| 22 | cli | formats(5) feedback(3) integration(2) shape(1) | 11 | NOT STARTED | Uses anyhow |
| 23 | benches | 4 files | 9 | NOT STARTED | Bench code |
| 24 | echidna-bridge | types(4) tactic(2) cache(1) | 7 | NOT STARTED | |
| 25 | ir | types(2) lib(2) constraints(2) | 6 | NOT STARTED | |
| 26 | examples | 2 files | 5 | NOT STARTED | Example code |
| 27 | pyo3-codegen | optimized(2) module(1) | 3 | NOT STARTED | |
| 28 | security-bridge | runtime_verify(3) | 3 | NOT STARTED | |
| 29 | distributed | resilience(1) | 1 | NOT STARTED | |

## Progress Summary

- **Total crates:** 29 (grouped from 35 workspace members)
- **Completed:** 1/29 (messagepack-analyzer committed)
- **In progress:** 1/29 (rescript-analyzer — src/ done, tests/examples remain)
- **unwrap() remaining:** ~836
- **unwrap() removed:** ~96 (56 messagepack + ~40 rescript src/)

## Session Log

### Session 1 — 2026-03-30
- Created progress tracker
- Assessed error handling landscape
- **DONE: messagepack-analyzer** — 56 unwrap()→expect() in 4 test files. 0 production unwraps (only unwrap_or). 2 doc-comment unwraps left (standard practice). cargo check clean. COMMITTED.
- **IN PROGRESS: rescript-analyzer** — src/ files all done (ephapax_bridge.rs, converter.rs, lib.rs, parser.rs). **REMAINING: tests/interop_tests.rs (33 unwraps) and examples/basic_usage.rs (8 unwraps). These are NOT YET EDITED.** Production code had 0 real unwrap()s (all were unwrap_or/unwrap_or_default). NOT YET COMMITTED — changes staged but not committed.
- Session ended due to credit limit. Next agent: finish interop_tests.rs + basic_usage.rs, cargo check, commit, then proceed to shape-ir (Crate #3).

## Pickup Instructions for New Agents

1. Read THIS file first
2. Check which crate is marked IN PROGRESS or next NOT STARTED
3. Read the crate's existing error type (grep for `enum.*Error` in its src/)
4. For each file in the crate:
   - Read the file
   - Replace `.unwrap()` in production code with `?` / `map_err` / error variants
   - Replace `.unwrap()` in test code with `.expect("descriptive message")`
   - Ensure the file compiles (check return types match)
5. Run `cargo check -p <crate-name>` after each crate
6. Update this tracker: mark DONE, update counts
7. Commit after each crate with message: `refactor(<crate>): replace unwrap() with proper error handling`
