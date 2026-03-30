# TEST-NEEDS.md — protocol-squisher

> Generated 2026-03-29 by punishing audit.

## Current State

| Category     | Count | Notes |
|-------------|-------|-------|
| Unit tests   | ~65+  | Inline `#[test]` across crates: compat (ephapax_engine(4), bidirectional(8), compare(7), lib(10), schema(6), transport(17)), ir (constraints(3), lib(2), schema(3)), main lib(3). Elixir: 9 test files (crawler, config, format_detector, schema_sink, schema_parser, parallel_parser, empirical_db, pattern_extractor, mix tasks) |
| Integration  | 2     | Zig FFI integration_test, ReScript interop_test |
| E2E          | 0     | None |
| Benchmarks   | 4     | container_operations.rs, generated_vs_handwritten.rs, optimizer_bench.rs, shape_ir/shape_benchmarks.rs — ALL REAL, substantial |

**Source modules:** ~183 Rust source files across main + crates (compat, ir, rescript-analyzer, shape-ir) + Elixir crawler + Zig FFI + Idris2 ABI.

## What's Missing

### P2P (Property-Based) Tests
- [ ] Schema comparison: property tests for comparison symmetry and transitivity
- [ ] Bidirectional compatibility: A compat B implies constraints on B compat A
- [ ] Transport class: property tests for lattice properties (join, meet)
- [ ] Shape IR: property tests for IR transformation correctness

### E2E Tests
- [ ] Full protocol analysis: input schema -> parse -> IR -> compare -> compatibility report
- [ ] Crawler: discover endpoint -> fetch schema -> parse -> store -> report
- [ ] Cross-format: same protocol in different formats (OpenAPI, Protobuf, GraphQL) produces consistent results
- [ ] ReScript binding: full analysis through ReScript API

### Aspect Tests
- **Security:** No tests for malicious schema injection, crawler SSRF, schema size DoS
- **Performance:** Benchmarks are REAL and COMPREHENSIVE (good). Missing: crawler throughput, parallel analysis scaling
- **Concurrency:** No tests for parallel schema analysis, concurrent crawler operations
- **Error handling:** No tests for malformed schemas, unreachable endpoints, invalid protocol definitions

### Build & Execution
- [ ] `cargo test` across all crates
- [ ] `cargo bench` execution
- [ ] `mix test` for crawler
- [ ] Zig FFI tests

### Benchmarks Needed (Existing + Missing)
- [x] Container operations (EXISTS, real)
- [x] Generated vs handwritten (EXISTS, real)
- [x] Optimizer (EXISTS, real)
- [x] Shape IR (EXISTS, real)
- [ ] Crawler discovery + fetch throughput
- [ ] Full pipeline end-to-end latency
- [ ] Memory usage per schema complexity

### Self-Tests
- [ ] Analyze its own API surface
- [ ] Schema self-validation
- [ ] Transport class lattice consistency

## Priority

**MEDIUM-HIGH.** 183 source files with ~65+ inline tests + 9 Elixir test files = reasonable coverage for the core logic. Benchmarks are genuinely good — 4 real benchmark suites. Main gaps: ZERO E2E testing, no crawler integration tests, no security tests for a tool that fetches external schemas. The Elixir crawler is decently tested. The Rust compat crate has strong unit tests. Integration is the missing layer.
