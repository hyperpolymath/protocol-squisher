; SPDX-License-Identifier: PMPL-1.0-or-later
; SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

; Concorde class constraint verification.
;
; Verifies that Concorde class is assigned if and only if types are
; identical, and that safe widening implies size ordering.
;
; Expected result: unsat for each check (confirming constraints hold).

; ── Type definitions (inlined for standalone execution) ─────────────────────

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

; ── CHECK 1: Concorde ↔ identical types ─────────────────────────────────────
;
; Assert: there exists a pair where Concorde is assigned but types differ.
; Expected: unsat (Concorde only for identical types).

(push)
(declare-const s1 PrimitiveType)
(declare-const t1 PrimitiveType)
(assert (and
  (= (transport_class s1 t1) Concorde)
  (not (= s1 t1))))
(check-sat)
; Expected: unsat
(pop)

; ── CHECK 2: safe widening implies sizeof(source) < sizeof(target) ──────────
;
; Assert: there exists a pair where safe_widening holds but
; sizeof(source) >= sizeof(target).
; Expected: unsat (widening always goes to a larger type).

(push)
(declare-const s2 PrimitiveType)
(declare-const t2 PrimitiveType)
(assert (and
  (safe_widening s2 t2)
  (>= (sizeof s2) (sizeof t2))))
(check-sat)
; Expected: unsat
(pop)

; ── CHECK 3: safe widening is irreflexive ───────────────────────────────────
;
; Assert: there exists a type that widens to itself.
; Expected: unsat (no type widens to itself).

(push)
(declare-const s3 PrimitiveType)
(assert (safe_widening s3 s3))
(check-sat)
; Expected: unsat
(pop)

; ── CHECK 4: safe widening pairs get Business class ─────────────────────────
;
; Assert: there exists a widening pair that does NOT get Business.
; Expected: unsat (all widening pairs are Business).

(push)
(declare-const s4 PrimitiveType)
(declare-const t4 PrimitiveType)
(assert (and
  (safe_widening s4 t4)
  (not (= (transport_class s4 t4) Business))))
(check-sat)
; Expected: unsat
(pop)
