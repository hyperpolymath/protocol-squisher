; SPDX-License-Identifier: PMPL-1.0-or-later
; SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

; Core type declarations for Protocol Squisher SMT proofs.
; Mirrors the Agda Types.agda definitions.

; ── Primitive Type enumeration ──────────────────────────────────────────────

(declare-datatypes () ((PrimitiveType
  I8 I16 I32 I64 I128
  U8 U16 U32 U64 U128
  F32 F64
  Bool_
  String_)))

; ── Transport Class enumeration ─────────────────────────────────────────────

(declare-datatypes () ((TransportClass
  Concorde
  Business
  Economy
  Wheelbarrow)))

; ── Size function (in bits) ─────────────────────────────────────────────────

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
  0))))))))))))))  ; String = 0 (variable)

; ── Safe widening predicate ─────────────────────────────────────────────────

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

; ── Transport class assignment ──────────────────────────────────────────────

(define-fun transport_class ((s PrimitiveType) (t PrimitiveType)) TransportClass
  (ite (= s t) Concorde
  (ite (safe_widening s t) Business
  Wheelbarrow)))
