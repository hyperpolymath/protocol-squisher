;; SPDX-License-Identifier: PMPL-1.0-or-later
;; ECOSYSTEM.scm - Ecosystem Positioning
;; protocol-squisher
;;
;; IMPORTANT: Satellite relationships must be kept up to date.
;; When adding/removing satellites, update this file and the satellite's ECOSYSTEM.scm.

(ecosystem
  (version . "1.2.0")
  (name . "protocol-squisher")
  (type . "library + research-tool")
  (purpose . "Universal data shape reasoning engine — formally reason about data structure across serialization formats, databases, APIs, type systems, and memory layouts, with algebraic guarantees")

  (position-in-ecosystem
   (category . "developer-tools + foundational-research")
   (layer . "interoperability + data-shape-algebra")
   (vision . "18-month plan: format converter → universal data shape reasoning engine (VISION-18-MONTHS.md)"))

  (related-projects
   ((name . "ephapax")
    (relationship . "core-dependency")
    (note . "Linear type system - canonical IR implemented in ephapax with Idris2 dependent types for zero-copy safety proofs"))
   ((name . "ECHIDNA")
    (relationship . "verification-platform")
    (note . "Neurosymbolic theorem proving platform - formal verification of transport class analysis (Agda, Lean, Coq integration)"))
   ((name . "serde")
    (relationship . "dependency")
    (note . "Rust serialization framework - source format"))
   ((name . "pydantic")
    (relationship . "target-integration")
    (note . "Python validation library - target format"))
   ((name . "PyO3")
    (relationship . "dependency")
    (note . "Rust-Python FFI bindings for generated adapters"))
   ((name . "proven")
    (relationship . "sibling-standard")
    (note . "Formal verification for adapter correctness proofs"))
   ((name . "Idris2")
    (relationship . "verification-language")
    (note . "Dependently-typed language used for ephapax IR implementation with totality checking"))
   ;; New related projects (vision direction)
   ((name . "Cambria")
    (relationship . "inspiration")
    (note . "Ink & Switch lens-based system for evolving JSON schemas in local-first software — closest existing system to our vision, but we generalise beyond JSON"))
   ((name . "Apache Arrow")
    (relationship . "potential-consumer")
    (note . "Columnar in-memory format with well-defined type system — Arrow schemas are data shapes, Phase 3 will include an Arrow extractor"))
   ((name . "buf.build")
    (relationship . "inspiration")
    (note . "Protobuf schema management with breaking change detection — does for Protobuf what we aim to do for all data shapes"))
   ((name . "CUE")
    (relationship . "inspiration")
    (note . "Constraint-based configuration language with lattice-based type system — philosophically aligned with our linearity lattice and transport class semilattice"))
   ((name . "BX community")
    (relationship . "academic-foundation")
    (note . "Bidirectional transformations research (symmetric lenses, delta lenses) — theoretical foundation for our morphism algebra"))))

  (what-this-is
   "A universal data shape reasoning engine with algebraic guarantees"
   "A code generator that synthesizes type-safe adapters between serialization formats"
   "A compatibility analyzer that classifies format pairs by transport class (Concorde/Business/Economy/Wheelbarrow)"
   "A formal guarantee system: if it compiles, data will transport (even if lossy)"
   "A JSON fallback mechanism that ensures universal compatibility"
   "A performance optimizer that generates zero-copy paths when possible"
   "(Vision) A category-theoretic foundation for reasoning about data shape across all structural boundaries")

  (what-this-is-not
   "Not an RPC framework - focuses on data serialization only"
   "Not a runtime library - generates standalone adapter code"
   "Not a schema registry - analyzes schemas but doesn't store them"
   "Not a format converter CLI - generates code for integration, not one-off conversions"
   "Not a replacement for manual FFI when performance is critical")

  ;; Maintenance note: Review satellite relationships when:
  ;; - Adding new repos with similar suffix patterns (-ssg, -mcp, -scm, -ffi)
  ;; - Removing or archiving repos
  ;; - Changing the portfolio structure
  (maintenance-checks
   (satellite-sync . "Ensure parent and satellite ECOSYSTEM.scm files are consistent")
   (portfolio-review . "Verify all satellites are listed in parent repo")))
