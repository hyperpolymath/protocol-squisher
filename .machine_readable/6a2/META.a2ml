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
      (decision . "Use canonical IR as lingua franca between all protocols")
      (consequences . "N-to-M protocol interoperability scales as analyzers plus generators."))
    (adr-002
      (status . "accepted")
      (date . "2026-01-04")
      (decision . "Preserve universal transport with JSON fallback")
      (consequences . "Wheelbarrow path is slower and potentially lossy, but transport never hard-fails."))
    (adr-003
      (status . "accepted")
      (date . "2026-01-04")
      (decision . "Classify compatibility by transport classes")
      (consequences . "Users see fidelity and performance tradeoffs before generating adapters."))
    (adr-004
      (status . "accepted")
      (date . "2026-02-04")
      (decision . "Implement canonical IR in ephapax with Idris2 proofs")
      (consequences . "Critical IR invariants gain compile-time guarantees for zero-copy safety."))
    (adr-005
      (status . "accepted")
      (date . "2026-02-24")
      (decision . "Use Zig-backed FFI boundaries for ephapax bridge paths")
      (consequences . "FFI surface stays explicit and testable; panic-assail checks remain enforceable."))
    (adr-006
      (status . "accepted")
      (date . "2026-02-24")
      (decision . "Treat machine-readable SCM files under .machines_readable/6scm as the source of truth")
      (consequences . "Automation and human docs remain aligned through single-location governance metadata."))))

(define development-practices
  '((code-style
      (formatter . "rustfmt")
      (linter . "clippy")
      (rust-edition . "2021")
      (rust-version . "1.86"))
    (testing
      (unit-tests . "Required for all crates")
      (integration-tests . "Required for protocol and FFI bridges")
      (property-tests . "Required for IR and compatibility invariants")
      (fuzzing . "ClusterFuzzLite plus panic-assail regression"))
    (security
      (spdx-required . #t)
      (sha-pinning . #t)
      (codeql-enabled . #t)
      (scorecard-enabled . #t)
      (dependabot-enabled . #t))
    (containerization
      (runtime . "podman")
      (compose . "podman compose or podman-compose"))
    (documentation
      (human-readable . ("README.adoc" "ROADMAP.adoc" "docs/"))
      (machine-readable . ".machines_readable/6scm"))))

(define design-rationale
  '((why-rust
      "Strong type safety, predictable performance, and mature tooling for analyzers and generators.")
    (why-idris2-ephapax
      "Dependent typing and totality checks enforce IR safety properties that are hard to guarantee in tests alone.")
    (why-zig-ffi
      "A narrow Zig FFI boundary keeps ABI details explicit and easier to audit.")
    (why-transport-classes
      "Explicit fidelity and overhead categories prevent hidden conversion surprises.")
    (why-machine-readable-governance
      "Structured metadata supports deterministic automation and keeps agents aligned with project intent.")))

(define repository-requirements
  '((mandatory-dotfiles
      ".gitignore"
      ".gitattributes"
      ".editorconfig"
      ".tool-versions")
    (machine-readable-root
      ".machines_readable/6scm")
    (mandatory-scm-files
      "META.scm"
      "STATE.scm"
      "ECOSYSTEM.scm"
      "PLAYBOOK.scm"
      "AGENTIC.scm"
      "NEUROSYM.scm")
    (build-system
      (task-runner . "Justfile")
      (state-contract . "Mustfile")
      (forbidden . ("Makefile")))))
