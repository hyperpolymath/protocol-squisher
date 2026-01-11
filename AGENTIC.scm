;; SPDX-License-Identifier: PMPL-1.0
;; AGENTIC.scm - AI Agent Operational Gating
;; protocol-squisher

(define-module (protocol_squisher agentic)
  #:export (agentic-config))

(define agentic-config
  '((version . "1.0.0")
    (name . "protocol-squisher")
    (entropy-budget . 0.3)
    (allowed-operations . (read analyze suggest))
    (forbidden-operations . ())
    (gating-rules . ())))
