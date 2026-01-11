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
  '((phase . "phase-0-week-2")
    (overall-completion . 50)
    (components
     ((protocol-squisher-ir . 90)
      (protocol-squisher-cli . 30)
      (protocol-squisher-rust-analyzer . 85)
      (protocol-squisher-python-analyzer . 0)
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
      "Struct and enum extraction from Rust source"))))

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
       ((todo "Python introspection script for Pydantic")
        (todo "Parse introspection output in Rust")
        (todo "Convert to IR")))
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
     ("Wire up CLI to use Rust analyzer"
      "Test with real-world serde examples"))
    (this-week
     ("Start protocol-squisher-python-analyzer crate"
      "Pydantic introspection"))
    (this-month
     ("Complete Phase 0 (all 4 weeks)"
      "Have working Python analyzer"))))

(define session-history
  '(((date . "2026-01-11")
     (duration . "2 sessions")
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
       "31 total tests across workspace"
       "All code compiles and tests pass")))))
