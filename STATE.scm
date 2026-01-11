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
  '((phase . "phase-0-week-3")
    (overall-completion . 75)
    (components
     ((protocol-squisher-ir . 90)
      (protocol-squisher-cli . 30)
      (protocol-squisher-rust-analyzer . 85)
      (protocol-squisher-python-analyzer . 85)
      (protocol-squisher-compat . 0)))
    (working-features
     ("IR type system (primitives, containers, composites)"
      "IR constraint system"
      "IR JSON serialization/deserialization"
      "Schema validation"
      "Topological sort for type dependencies"
      "CLI skeleton (analyze, generate commands)"
      "Rust source file parsing (syn crate)"
      "Serde attribute parsing (#[serde(rename, tag, etc)])"
      "Type conversion (primitives, containers, references)"
      "Struct and enum extraction from Rust source"
      "Python introspection script for Pydantic v1/v2"
      "JSON parsing of Python introspection output"
      "Pydantic model to IR struct conversion"
      "Python enum to IR enum conversion"
      "Constraint extraction (ge, le, min/max_length, pattern)"))))

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
       ((todo "IR comparison algorithm")
        (todo "Type compatibility rules")
        (todo "Classification scoring")
        (todo "Loss documentation")))))))

(define blockers-and-issues
  '((critical . ())
    (high . ())
    (medium
     (("rust-version" . "Using Rust 1.75, some deps require newer")))
    (low . ())))

(define critical-next-actions
  '((immediate
     ("Wire up CLI to use analyzers"
      "Test with real-world examples"))
    (this-week
     ("Start protocol-squisher-compat crate"
      "IR comparison algorithm"))
    (this-month
     ("Complete Phase 0 Week 4"
      "Have working compatibility engine"))))

(define session-history
  '(((date . "2026-01-11")
     (duration . "3 sessions")
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
       "48 total tests across workspace"
       "All code compiles and tests pass")))))
