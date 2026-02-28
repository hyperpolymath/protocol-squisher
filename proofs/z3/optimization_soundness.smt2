; SPDX-License-Identifier: PMPL-1.0-or-later
; SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

; Optimization soundness verification via SMT.
;
; Cross-validates the Agda OptimizationSoundness proof:
;   1. Safe widening never produces Wheelbarrow class
;   2. Safe widening always produces Business class
;   3. Roundtrip property: sizeof(source) <= sizeof(target) for widening
;
; Expected results: unsat for each check (confirming properties hold).

; ── Type definitions (inlined for standalone execution) ───────────────

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

(define-fun sizeof ((t PrimitiveType)) Int
  (ite (= t I8) 8
  (ite (= t I16) 16
  (ite (= t I32) 32
  (ite (= t I64) 64
  (ite (= t I128) 128
  (ite (= t U8) 8
  (ite (= t U16) 16
  (ite (= t U32) 32
  (ite (= t U64) 64
  (ite (= t U128) 128
  (ite (= t F32) 32
  (ite (= t F64) 64
  (ite (= t Bool_) 1
  0))))))))))))))

(define-fun safe_widening ((s PrimitiveType) (t PrimitiveType)) Bool
  (or
    ; Signed integer widening
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
    ; Unsigned integer widening
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
    ; Float widening
    (and (= s F32) (= t F64))))

(define-fun transport_class ((s PrimitiveType) (t PrimitiveType)) TransportClass
  (ite (= s t) Concorde
  (ite (safe_widening s t) Business
  Wheelbarrow)))

; ── CHECK 1: Widening never produces Wheelbarrow ─────────────────────
;
; Assert: there exists a widening pair classified as Wheelbarrow.
; Expected: unsat (widening always yields Business, never Wheelbarrow).

(push)
(declare-const s1 PrimitiveType)
(declare-const t1 PrimitiveType)
(assert (and
  (safe_widening s1 t1)
  (= (transport_class s1 t1) Wheelbarrow)))
(check-sat)
; Expected: unsat
(pop)

; ── CHECK 2: Widening always produces Business ───────────────────────
;
; Assert: there exists a widening pair that does NOT get Business.
; Expected: unsat (all widening pairs are Business class).

(push)
(declare-const s2 PrimitiveType)
(declare-const t2 PrimitiveType)
(assert (and
  (safe_widening s2 t2)
  (not (= (transport_class s2 t2) Business))))
(check-sat)
; Expected: unsat
(pop)

; ── CHECK 3: Roundtrip size property ─────────────────────────────────
;
; Assert: there exists a widening pair where source size > target size.
; Expected: unsat (widening always goes to a strictly larger type,
; so every value representable in source fits in target).

(push)
(declare-const s3 PrimitiveType)
(declare-const t3 PrimitiveType)
(assert (and
  (safe_widening s3 t3)
  (>= (sizeof s3) (sizeof t3))))
(check-sat)
; Expected: unsat
(pop)

; ── CHECK 4: Non-widening non-identity is Wheelbarrow ────────────────
;
; Assert: there exists a pair that is neither identical nor widening,
; yet avoids Wheelbarrow.
; Expected: unsat (confirms optimizer taxonomy is complete).

(push)
(declare-const s4 PrimitiveType)
(declare-const t4 PrimitiveType)
(assert (and
  (not (= s4 t4))
  (not (safe_widening s4 t4))
  (not (= (transport_class s4 t4) Wheelbarrow))))
(check-sat)
; Expected: unsat
(pop)

; ── CHECK 5: Widening is asymmetric ──────────────────────────────────
;
; Assert: there exists a pair where both directions are safe widening.
; Expected: unsat (widening is strictly one-directional).

(push)
(declare-const s5 PrimitiveType)
(declare-const t5 PrimitiveType)
(assert (and
  (safe_widening s5 t5)
  (safe_widening t5 s5)))
(check-sat)
; Expected: unsat
(pop)
