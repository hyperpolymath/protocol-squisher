;; SPDX-License-Identifier: PMPL-1.0-or-later
;; META.scm - Architecture Decisions and Development Practices
;; protocol-squisher

(define-module (protocol_squisher meta)
  #:export (architecture-decisions
            development-practices
            design-rationale
            repository-requirements))

(define architecture-decisions
  '())

(define development-practices
  '((code-style
     (formatter . "deno fmt")
     (linter . "deno lint"))
    (versioning
     (scheme . "Semantic Versioning 2.0.0"))
    (documentation
     (format . "AsciiDoc"))
    (security
     (spdx-required . #t)
     (sha-pinning . #t))))

(define design-rationale
  '())

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
