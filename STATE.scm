;; SPDX-License-Identifier: PMPL-1.0
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
    (updated . "2026-01-11")
    (project . "protocol-squisher")
    (repo . "hyperpolymath/protocol-squisher")))

(define project-context
  '((name . "protocol-squisher")
    (tagline . "Universal protocol interoperability through automatic adapter synthesis")
    (tech-stack . (rust serde proptest))))

(define current-position
  '((phase . "phase-1-optimization-layer")
    (overall-completion . 85)
    (components
     ((protocol-squisher-ir . 95)
      (protocol-squisher-cli . 100)
      (protocol-squisher-rust-analyzer . 95)
      (protocol-squisher-python-analyzer . 90)
      (protocol-squisher-compat . 95)
      (protocol-squisher-pyo3-codegen . 100)
      (protocol-squisher-json-fallback . 100)
      (protocol-squisher-optimizer . 20)))
    (working-features
     ("IR type system (primitives, containers, composites)"
      "IR constraint system"
      "IR JSON serialization/deserialization"
      "Schema validation"
      "Topological sort for type dependencies"
      "Full CLI with analyze, compare, generate commands"
      "Rust source file parsing (syn crate)"
      "Serde attribute parsing (#[serde(rename, tag, etc)])"
      "Type conversion (primitives, containers, references)"
      "Struct and enum extraction from Rust source"
      "Python introspection script for Pydantic v1/v2"
      "JSON parsing of Python introspection output"
      "Pydantic model to IR struct conversion"
      "Python enum to IR enum conversion"
      "Constraint extraction (ge, le, min/max_length, pattern)"
      "Transport class classification (Concorde, BusinessClass, Economy, Wheelbarrow, Incompatible)"
      "IR type comparison with widening/narrowing detection"
      "Schema-level comparison with field/variant analysis"
      "Conversion loss documentation (kind, path, severity, description)"
      "PyO3 struct generation with getters/setters"
      "PyO3 enum generation with match arms"
      "Python stub (.pyi) generation"
      "Type mapping (Rust -> Python)"
      "103 total tests across workspace"))))

(define route-to-mvp
  '((milestones
     ((week-1 "Canonical IR"
       ((done "Design intermediate representation")
        (done "Implement type system")
        (done "Constraint representation")
        (done "IR <-> JSON serialization")
        (done "Property-based tests for IR invariants")))
      (week-2 "Rust Analyzer"
       ((done "Parse Rust source files (syn crate)")
        (done "Extract serde types")
        (done "Convert to IR")
        (done "Handle common patterns")))
      (week-3 "Python Analyzer"
       ((done "Python introspection script for Pydantic")
        (done "Parse introspection output in Rust")
        (done "Convert to IR")))
      (week-4 "Compatibility Engine"
       ((done "IR comparison algorithm")
        (done "Type compatibility rules")
        (done "Classification scoring")
        (done "Loss documentation")))
      (phase-1 "PyO3 Code Generator"
       ((done "Struct generation with PyO3 derives")
        (done "Enum generation with match arms")
        (done "Type mapping (Rust primitives -> Python)")
        (done "Optional field handling")
        (done "Python stub (.pyi) generation")
        (done "Module generation with exports")
        (done "28 passing tests in pyo3-codegen")))
      (phase-2 "CLI Integration"
       ((done "Wire all analyzer crates into CLI")
        (done "analyze command - parse and display IR")
        (done "compare command - schema compatibility with losses")
        (done "generate command - PyO3 binding generation")
        (done "Sample schemas for testing")
        (done "103 total tests across workspace")))))))

(define blockers-and-issues
  '((critical . ())
    (high . ())
    (medium
     (("rust-version" . "Using Rust 1.75, some deps require newer")))
    (low . ())))

(define critical-next-actions
  '((immediate
     ("Complete optimization layer (protocol-squisher-optimizer)"
      "Detect zero-copy opportunities"
      "Benchmark against JSON fallback"))
    (this-week
     ("Test with real-world protocol schemas"
      "JSON Schema analyzer"
      "Performance benchmarks"))
    (this-month
     ("Full end-to-end Rust<->Python interop demo"
      "Protobuf analyzer"
      "CLI polish and documentation"
      "Publish to crates.io"))
    (out-of-scope
     ("Semantic transport layer - separate project (see proven/SafeForth)"))))

(define session-history
  '(((date . "2026-01-11")
     (duration . "6 sessions")
     (accomplishments
      ("Created src/ directory with lib.rs and main.rs"
       "Implemented protocol-squisher-ir crate"
       "Full type system: primitives, containers, composites"
       "Constraint system with 30+ constraint types"
       "Schema validation and topological sorting"
       "11 passing unit tests"
       "CLI skeleton with help, analyze, generate commands"
       ;; Week 2 additions
       "Implemented protocol-squisher-rust-analyzer crate"
       "Rust source parsing with syn crate"
       "Serde attribute extraction (rename, tag, content, skip, flatten, etc)"
       "Type conversion: primitives, containers, smart pointers, cells"
       "Struct analysis with field extraction"
       "Enum analysis with variant payloads"
       "Tag style detection (external, internal, adjacent, untagged)"
       "20 passing tests in rust-analyzer"
       ;; Week 3 additions
       "Implemented protocol-squisher-python-analyzer crate"
       "Python introspection script supporting Pydantic v1 and v2"
       "Type parsing: primitives, Optional, Union, List, Dict, Tuple"
       "Pydantic model and enum extraction"
       "Field constraint extraction (ge, le, min/max_length, pattern)"
       "Nested model reference handling"
       "17 passing tests in python-analyzer"
       ;; Week 4 additions
       "Implemented protocol-squisher-compat crate"
       "Transport class system (Concorde, BusinessClass, Economy, Wheelbarrow, Incompatible)"
       "IR type comparison: primitive widening/narrowing, container conversions"
       "Schema-level comparison with field and variant analysis"
       "Conversion loss documentation (kind, path, severity, description)"
       "LossKind enum: 13 loss types (precision, range, encoding, etc)"
       "LossSeverity enum: Info, Minor, Moderate, Major, Critical"
       "27 passing tests in compat crate"
       "75 total tests across workspace"
       "Phase 0 complete - all weeks done"
       ;; Phase 1 - PyO3 Codegen
       "Implemented protocol-squisher-pyo3-codegen crate"
       "PyO3 struct generation with #[pyclass] and #[pymethods]"
       "PyO3 enum generation with match arms for variants"
       "Type mapping: Rust primitives to Python (i32->int, f64->float, etc)"
       "Optional field handling with Option<T> wrapping"
       "Python stub (.pyi) generation for type hints"
       "Module generation with #[pymodule] exports"
       "Fixed test compilation: removed invalid discriminant field"
       "Fixed TagStyle::Internal { tag_field: } syntax"
       "28 passing tests in pyo3-codegen"
       ;; Phase 2 - CLI Integration
       "Wired all analyzer crates into main CLI binary"
       "Re-exported crates in src/lib.rs"
       "Full analyze command: parse .rs/.py/.json files, display IR"
       "Full compare command: schema compatibility with loss reporting"
       "Full generate command: PyO3 binding generation"
       "Created docs/samples/ with example schemas"
       "user.rs and user_v2.rs for testing compare command"
       "103 total tests across workspace"
       "Phase 1 and Phase 2 complete")))))
