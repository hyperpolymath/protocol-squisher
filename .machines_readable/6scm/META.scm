;; SPDX-License-Identifier: PMPL-1.0-or-later
;; META.scm - Architecture Decisions and Development Practices
;; protocol-squisher

(define-module (protocol_squisher meta)
  #:export (architecture-decisions
            development-practices
            design-rationale
            repository-requirements))

(define architecture-decisions
  '((adr-001
      (status . "accepted")
      (date . "2026-01-04")
      (context . "Need universal approach to serialization format incompatibility")
      (decision . "Use canonical IR as lingua franca between all formats")
      (consequences . "All analyzers map to IR, all generators consume IR. Enables N-to-M format support with N+M analyzers instead of N*M converters."))
    (adr-002
      (status . "accepted")
      (date . "2026-01-04")
      (context . "Some format pairs are fundamentally incompatible at type level")
      (decision . "JSON fallback guarantees transport for all format pairs (the wheelbarrow)")
      (consequences . "Slow and lossy, but universal. Never block on type incompatibility. Document losses upfront."))
    (adr-003
      (status . "accepted")
      (date . "2026-01-04")
      (context . "Need to set user expectations about adapter quality")
      (decision . "Classify format pairs into transport classes: Concorde (perfect), Business (minor overhead), Economy (moderate loss), Wheelbarrow (high loss)")
      (consequences . "Users know what they're getting. No surprise performance degradation."))
    (adr-004
      (status . "accepted")
      (date . "2026-01-04")
      (context . "Python↔Rust FFI is painful and error-prone")
      (decision . "Start with PyO3 adapter generation as MVP use case")
      (consequences . "High impact, proves invariant, addresses real pain point. Rust+Python is most valuable first target."))
    (adr-005
      (status . "accepted")
      (date . "2026-01-04")
      (context . "Generated code quality matters for adoption")
      (decision . "Generated adapters must pass clippy, mypy, and property-based tests")
      (consequences . "Higher bar for code generation, but professional quality output."))
    (adr-006
      (status . "accepted")
      (date . "2026-01-04")
      (context . "Need to prove correctness of adapters")
      (decision . "Use property-based testing (proptest) plus future formal verification (miniKanren)")
      (consequences . "Exhaustive test coverage. Path to formal proofs in Phase 3."))
    (adr-007
      (status . "accepted")
      (date . "2026-02-04")
      (context . "Need to validate ephapax with real-world programs and ensure zero-copy safety in IR")
      (decision . "Implement canonical IR in ephapax instead of plain Rust")
      (consequences . "Linear types prove zero-copy paths safe. No aliasing bugs in generated adapters. Memory safety at FFI boundaries proven at compile time. Serves as real-world ephapax validation. Adds compilation dependency on ephapax → WASM → Rust FFI pipeline."))))

(define development-practices
  '((code-style
     (formatter . "rustfmt")
     (linter . "clippy")
     (rust-edition . "2021")
     (rust-version . "1.83"))
    (testing
     (unit-tests . "Required for all modules")
     (property-tests . "Required for IR and adapters (proptest)")
     (integration-tests . "PyO3 integration tests with maturin")
     (fuzzing . "ClusterFuzzLite for security"))
    (versioning
     (scheme . "Semantic Versioning 2.0.0"))
    (documentation
     (format . "AsciiDoc")
     (readme . "README.adoc")
     (roadmap . "ROADMAP.adoc")
     (gauntlet . "GAUNTLET.adoc"))
    (security
     (spdx-required . #t)
     (sha-pinning . #t)
     (hypatia-scanning . #t)
     (scorecard-compliance . #t))
    (performance
     (benchmarking . "criterion with HTML reports")
     (release-profile . "LTO enabled, stripped binaries"))))

(define design-rationale
  '((why-rust
      "Rust provides type safety, zero-cost abstractions, and excellent FFI support. Code generation benefits from strong type system.")
    (why-ephapax-ir
      "Linear types prove zero-copy paths are safe. Resources freed exactly once (no leaks). Memory safety at FFI boundaries guaranteed at compile time. Serves as real-world validation of ephapax language.")
    (why-workspace-crates
      "Each analyzer/generator is independent. Enables parallel development and pluggable architecture for new formats.")
    (why-json-fallback
      "JSON is universal, human-readable, and every format can convert to it. Slow but guaranteed to work - the ultimate wheelbarrow.")
    (why-transport-classes
      "Users need honest communication about tradeoffs. Better to say 'this will be slow' upfront than surprise them later.")
    (why-canonical-ir
      "Single IR means N+M adapters instead of N*M. Optimizations to IR benefit all formats. Future AI/learning can target IR.")
    (why-property-testing
      "Serialization bugs are subtle. Property tests catch edge cases manual tests miss. Proves roundtrip fidelity.")
    (why-no-runtime-library
      "Generated code should be standalone and dependency-free. No lock-in, works in any environment.")
    (why-pyo3-first
      "Python↔Rust is highest impact use case. Proves concept with real-world value. PyO3 is mature and well-documented.")))

;; IMPORTANT: These requirements must always be kept up to date
(define repository-requirements
  '((mandatory-dotfiles
     ".gitignore"
     ".gitattributes"
     ".editorconfig"
     ".tool-versions")
    (mandatory-scm-files
     "META.scm"
     "STATE.scm"
     "ECOSYSTEM.scm"
     "PLAYBOOK.scm"
     "AGENTIC.scm"
     "NEUROSYM.scm")
    (build-system
     (task-runner . "justfile")
     (state-contract . "Mustfile")
     (forbidden . ("Makefile")))
    (meta-directory
     ".meta/REQUIRED-FILES.md")
    (satellite-management
     (check-frequency . "on-new-repo")
     (sync-ecosystem . #t)
     (note . "When adding satellites, update ECOSYSTEM.scm in both parent and satellite"))))
