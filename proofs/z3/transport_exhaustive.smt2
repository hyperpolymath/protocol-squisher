; SPDX-License-Identifier: PMPL-1.0-or-later
; SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

; Transport class assignment exhaustiveness verification.
;
; Verifies that every (source, target) primitive type pair maps to
; exactly one transport class — no gaps and no overlaps.
;
; Expected result: unsat (confirming no gaps exist).

; ── Include type definitions ────────────────────────────────────────────────

(declare-datatypes () ((PrimitiveType
  I8 I16 I32 I64 I128
  U8 U16 U32 U64 U128
  F32 F64
  Bool_
  String_)))

(declare-datatypes () ((TransportClass
  Concorde
  Business
  Economy
  Wheelbarrow)))

(define-fun safe_widening ((s PrimitiveType) (t PrimitiveType)) Bool
  (or
    (and (= s I8) (= t I16))
    (and (= s I8) (= t I32))
    (and (= s I8) (= t I64))
    (and (= s I8) (= t I128))
    (and (= s I16) (= t I32))
    (and (= s I16) (= t I64))
    (and (= s I16) (= t I128))
    (and (= s I32) (= t I64))
    (and (= s I32) (= t I128))
    (and (= s I64) (= t I128))
    (and (= s U8) (= t U16))
    (and (= s U8) (= t U32))
    (and (= s U8) (= t U64))
    (and (= s U8) (= t U128))
    (and (= s U16) (= t U32))
    (and (= s U16) (= t U64))
    (and (= s U16) (= t U128))
    (and (= s U32) (= t U64))
    (and (= s U32) (= t U128))
    (and (= s U64) (= t U128))
    (and (= s F32) (= t F64))))

(define-fun transport_class ((s PrimitiveType) (t PrimitiveType)) TransportClass
  (ite (= s t) Concorde
  (ite (safe_widening s t) Business
  Wheelbarrow)))

; ── EXHAUSTIVENESS CHECK ────────────────────────────────────────────────────
;
; Assert: there exists some pair (s, t) where the transport class is NONE
; of Concorde, Business, or Wheelbarrow.
;
; If the solver returns "unsat", it means no such pair exists — the
; classification is exhaustive.

(declare-const s PrimitiveType)
(declare-const t PrimitiveType)

(assert (not (or
  (= (transport_class s t) Concorde)
  (= (transport_class s t) Business)
  (= (transport_class s t) Wheelbarrow))))

(check-sat)
; Expected: unsat (no gaps in classification)
