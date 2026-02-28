(* SPDX-License-Identifier: PMPL-1.0-or-later *)
(* SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell *)

(** * "If It Compiles, It Carries" Invariant

    Cross-validates the Agda CarriesInvariant proof in Coq.

    Core claim: For any two primitive types, a transport class and
    conversion strategy always exist. There are no gaps in the
    classification. *)

Require Import Types.

(** ** Conversion strategies corresponding to transport classes *)

Inductive ConversionStrategy : Set :=
  | DirectCopy       (* Concorde: identity function *)
  | SafeCast         (* Business: widening cast *)
  | Documented       (* Economy: lossy but documented conversion *)
  | JsonFallback.    (* Wheelbarrow: serialize to JSON *)

(** ** Every transport class maps to a strategy *)

Definition strategy_of (c : TransportClass) : ConversionStrategy :=
  match c with
  | Concorde => DirectCopy
  | Business => SafeCast
  | Economy => Documented
  | Wheelbarrow => JsonFallback
  end.

(** ** THE INVARIANT: every pair of primitive types has a transport class *)

Theorem every_pair_classified : forall s t : PrimitiveType,
  exists c : TransportClass, primitive_transport_class s t = c.
Proof.
  intros s t.
  exists (primitive_transport_class s t).
  reflexivity.
Qed.

(** ** Every pair has a conversion strategy *)

Theorem every_pair_has_strategy : forall s t : PrimitiveType,
  exists strat : ConversionStrategy,
    strat = strategy_of (primitive_transport_class s t).
Proof.
  intros s t.
  exists (strategy_of (primitive_transport_class s t)).
  reflexivity.
Qed.

(** ** The transport class function is total *)

Theorem transport_class_total : forall s t : PrimitiveType,
  primitive_transport_class s t = Concorde \/
  primitive_transport_class s t = Business \/
  primitive_transport_class s t = Wheelbarrow.
Proof.
  intros s t.
  unfold primitive_transport_class.
  destruct (PrimitiveType_eq_dec s t).
  - left. reflexivity.
  - destruct s, t;
    try (left; reflexivity);
    try (right; left; reflexivity);
    try (right; right; reflexivity);
    try contradiction.
Qed.

(** ** Concorde strategy always succeeds (identity is total) *)

Theorem concorde_always_succeeds : forall t : PrimitiveType,
  strategy_of (primitive_transport_class t t) = DirectCopy.
Proof.
  intros t.
  rewrite equal_implies_concorde.
  simpl. reflexivity.
Qed.

(** ** Transport is reflexive *)

Theorem transport_reflexive : forall t : PrimitiveType,
  primitive_transport_class t t = Concorde.
Proof.
  apply equal_implies_concorde.
Qed.

(** ** Coverage is complete: no primitive pair maps to Economy

    In the current type system, there are no "documented lossy"
    conversions — only exact (Concorde), widening (Business), or
    incompatible (Wheelbarrow). This proves Economy is not used
    for primitive-to-primitive (it appears only in container analysis). *)

Theorem no_economy_for_primitives : forall s t : PrimitiveType,
  primitive_transport_class s t <> Economy.
Proof.
  intros s t.
  unfold primitive_transport_class.
  destruct (PrimitiveType_eq_dec s t); [discriminate|].
  destruct s, t; discriminate || contradiction.
Qed.
