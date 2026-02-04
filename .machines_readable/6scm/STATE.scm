;; SPDX-License-Identifier: PMPL-1.0-or-later
;; STATE.scm - Project State and Progress
;; protocol-squisher

(define-module (protocol_squisher state)
  #:export (metadata
            project-context
            current-position
            route-to-mvp
            blockers-and-issues
            critical-next-actions
            session-history))

(define metadata
  '((version . "1.0.0")
    (schema-version . "1.0")
    (created . "2026-01-04")
    (updated . "2026-02-04")
    (project . "protocol-squisher")
    (repo . "hyperpolymath/protocol-squisher")))

(define project-context
  '((name . "protocol-squisher")
    (tagline . "Universal protocol interoperability through automatic adapter synthesis")
    (tech-stack . ("Rust" "PyO3" "serde" "syn" "proptest" "criterion"))))

(define current-position
  '((phase . "foundation")
    (overall-completion . 5)
    (components
      ((protocol-squisher-ir . "skeleton")
       (protocol-squisher-rust-analyzer . "skeleton")
       (protocol-squisher-python-analyzer . "skeleton")
       (protocol-squisher-compat . "skeleton")
       (protocol-squisher-pyo3-codegen . "skeleton")
       (protocol-squisher-json-fallback . "skeleton")
       (protocol-squisher-optimizer . "skeleton")
       (protocol-squisher-json-schema-analyzer . "skeleton")
       (protocol-squisher-protobuf-analyzer . "skeleton")))
    (working-features
      ("Project structure established"
       "PyO3 integration tests framework"
       "ClusterFuzzLite fuzzing setup"
       "CI/CD workflows (Hypatia, CodeQL, Scorecard)"))))

(define route-to-mvp
  '((milestones
      ((name . "Phase 0: Foundation")
        (weeks . "1-4")
        (items
          "Design canonical IR with type system"
          "Implement Rust analyzer (syn-based serde extraction)"
          "Implement Python analyzer (Pydantic introspection)"
          "Build compatibility engine with transport classification"))
       (name . "Phase 1: MVP")
        (weeks . "5-12")
        (items
          "JSON fallback mechanism (the wheelbarrow)"
          "PyO3 code generation for Rust↔Python"
          "Optimization layer for zero-copy paths"
          "CLI tool and documentation"
          "Public demo launch"))
       (name . "Phase 2: Format Expansion")
        (weeks . "13-24")
        (items
          "Add Cap'n Proto, Protobuf, Thrift, Avro analyzers"
          "Continuous learning system (schema crawler)"
          "Empirical compatibility database"))
       (name . "Phase 3: Production Readiness")
        (weeks . "25-52")
        (items
          "Formal verification with miniKanren"
          "Security protocol support"
          "FFI replacement capabilities"
          "Performance optimization (SIMD, zero-copy, streaming)"))))))

(define blockers-and-issues
  '((critical . ())
    (high . ())
    (medium . ())
    (low . ())))

(define critical-next-actions
  '((immediate
      "Define IR types in ephapax (types.eph) with linear annotations"
      "Implement compatibility analysis in ephapax (compat.eph)"
      "Set up Rust FFI wrapper for calling ephapax WASM modules"
      "Write property tests for linear type invariants")
    (this-week
      "Validate ephapax IR compiles to WASM (when ephapax-cli ready)"
      "Create Rust stubs for IR operations (until ephapax mature)"
      "Start Rust analyzer implementation using syn crate"
      "Design FFI boundary between Rust analyzers and ephapax IR")
    (this-month
      "Integrate ephapax → WASM → Rust FFI pipeline"
      "Finish Rust and Python analyzers"
      "Implement compatibility engine calling ephapax compat.eph"
      "Begin JSON fallback mechanism")))

(define session-history
  '())
