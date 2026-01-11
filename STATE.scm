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
    (updated . "2026-01-04")
    (project . "protocol-squisher")
    (repo . "hyperpolymath/protocol-squisher")))

(define project-context
  '((name . "protocol-squisher")
    (tagline . "")
    (tech-stack . ())))

(define current-position
  '((phase . "planning")
    (overall-completion . 0)
    (components . ())
    (working-features . ())))

(define route-to-mvp
  '((milestones . ())))

(define blockers-and-issues
  '((critical . ())
    (high . ())
    (medium . ())
    (low . ())))

(define critical-next-actions
  '((immediate . ())
    (this-week . ())
    (this-month . ())))

(define session-history
  '())
