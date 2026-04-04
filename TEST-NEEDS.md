# TEST-NEEDS.md — protocol-squisher

> Updated 2026-04-04: CRG C grade ACHIEVED. Test suite is comprehensive across unit, property-based, integration, and benchmark categories.

## Current State — CRG C ACHIEVED

| Category            | Count | Status   | Notes |
|---------------------|-------|----------|-------|
| **Total Passing**   | **1378** | ✓ PASSING | `cargo test --workspace` verified 2026-04-04 |
| Unit tests          | ~850+ | ✓ Complete | Inline `#[test]` across 50+ crates (compat, ir, shape-ir, analyzers, etc.) |
| Property-based      | 38+   | ✓ Complete | Dedicated `protocol-squisher-property-tests` crate (proptest framework) |
| Integration/E2E     | 66+   | ✓ Complete | Dedicated `protocol-squisher-integration-tests` crate — full pipeline (schema→IR→compare→report) |
| Security tests      | 40+   | ✓ Complete | Dedicated `protocol-squisher-security-bridge` crate — TLS negotiation, cert validation, audit |
| Benchmarks          | Real  | ✓ Complete | 6 Criterion benchmark suites: container_operations, generated_vs_handwritten, optimizer, shape_ir, transport_classes, analysis_throughput |
| Doc tests           | 8+    | ✓ Passing | shape-ir and protocol-squisher-thrift-analyzer documentation tests |

**Source modules:** ~183 Rust source files across main + crates + Elixir crawler + Zig FFI + Idris2 ABI.

## Test Categories (Verified 2026-04-04)

### Unit Tests (~850+)
- **compat crate**: ephapax_engine, bidirectional, compare, schema, transport modules
- **ir crate**: constraints, schema, extract, and library tests
- **shape-ir crate**: 165+ tests (124 unit + 36 property + 5 doc)
  - All 11 shape constructors tested
  - Comparison engine (symmetry, transitivity)
  - Shape extractors (SQL, OpenAPI, Arrow IPC)
  - Category laws and Dijkstra pathfinding
- **Analyzer crates** (17 total): OpenAPI, Protobuf, GraphQL, TOML, SQL DDL, etc.
- **Codegen crates**: PyO3, JSON fallback, Zig FFI
- **Elixir crawler**: 9 test files across multiple modules

### Property-Based Tests (38+)
**Dedicated crate**: `protocol-squisher-property-tests`
- **primitive_matrix**: All type combinations (i8→i128, u8→u128, f32↔f64, etc.)
- **container_combinations**: Nested arrays, maps, options, results, tuples
- **edge_cases**: Boundary conditions, empty schemas, circular references
- **Transport class lattice**: join/meet operations, idempotence, associativity
- **Bidirectional symmetry**: A compat B implications on B compat A

### Integration & E2E Tests (66+)
**Dedicated crate**: `protocol-squisher-integration-tests`
- Full pipeline: schema → IR → compare → compatibility report
- Multi-format consistency: same protocol in OpenAPI, Protobuf, GraphQL
- Concorde (zero-copy), Business (safe widening), Wheelbarrow (lossy) conversions
- Code generation verification: PyO3 and JSON fallback integration
- Nested structures and field-by-field analysis
- Cross-crate module initialization

### Security Tests (40+)
**Dedicated crate**: `protocol-squisher-security-bridge`
- TLS profile validation (v1.0–v1.3)
- Key exchange verification (RSA, DHE, ECDHE, PSK)
- Certificate chain validation
- Noise pattern mapping (NN, XX, IK, NK, KK)
- Security property verification (forward secrecy, mutual auth, replay resistance)
- Downgrade attack prevention
- Runtime verification protocols

### Benchmarks (6 suites, all REAL)
- **container_operations.rs**: Nested data structure conversion overhead
- **generated_vs_handwritten.rs**: Auto-generated vs manual code performance
- **optimizer_bench.rs**: Optimization algorithm efficiency
- **shape_benchmarks.rs**: Shape IR transformation latency
- **transport_classes.rs**: Transport class classification speed
- **analysis_throughput.rs**: Full-pipeline schema analysis throughput

### Doc Tests (8+)
- shape-ir module documentation tests
- protocol-squisher-thrift-analyzer compile tests

## CRG Certification

**Grade: C (ACHIEVED 2026-04-04)**
- 1378 passing tests across all categories
- Property-based testing framework in place (proptest)
- Integration test crate with full E2E scenarios
- Security-specific test suite
- Real Criterion benchmarks (6 suites)
- 100% test execution success rate
- All dangerous patterns banned (no believe_me, assert_total, Admitted, sorry, unsafeCoerce, etc.)

## Future Enhancements (Out of Scope for CRG C)

### Optional Additions (Phase 2+)
- [ ] Crawler throughput benchmarks (infrastructure-dependent)
- [ ] Parallel schema analysis scaling tests (distributed workload testing)
- [ ] Malicious schema injection tests (security hardening)
- [ ] Crawler SSRF mitigation tests (network isolation testing)
- [ ] Schema size DoS resistance tests (resource exhaustion scenarios)

### Why Not Blocking CRG C
CRG C requires: passing build, comprehensive unit/property/integration tests, real benchmarks, and no dangerous patterns. All met as of 2026-04-04. Phase 2+ enhancements add depth in specialized areas (distributed execution, malicious input hardening) that go beyond CRG C scope.
