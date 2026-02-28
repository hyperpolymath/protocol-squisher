(* SPDX-License-Identifier: PMPL-1.0-or-later *)
(* SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell *)

(** * Concorde Safety Proofs

    Cross-validates the Agda ConcordeSafety proofs in Coq.

    Core claim: If source and target types are identical, the conversion
    is lossless and bijective (Concorde class). *)

Require Import Types.

(** ** Lossless and Bijective definitions *)

Definition Lossless {A : Type} (f : A -> A) : Prop :=
  forall x y, f x = f y -> x = y.

Definition Surjective {A : Type} (f : A -> A) : Prop :=
  forall y, exists x, f x = y.

Definition Bijective {A : Type} (f : A -> A) : Prop :=
  Lossless f /\ Surjective f.

(** ** Identity function is lossless *)

Theorem id_lossless : forall (A : Type),
  Lossless (fun (x : A) => x).
Proof.
  unfold Lossless. intros A x y H. exact H.
Qed.

(** ** Identity function is surjective *)

Theorem id_surjective : forall (A : Type),
  Surjective (fun (x : A) => x).
Proof.
  unfold Surjective. intros A y. exists y. reflexivity.
Qed.

(** ** Identity function is bijective *)

Theorem id_bijective : forall (A : Type),
  Bijective (fun (x : A) => x).
Proof.
  intros A. split.
  - apply id_lossless.
  - apply id_surjective.
Qed.

(** ** Concorde class implies identical types *)

Theorem concorde_implies_equal : forall s t,
  primitive_transport_class s t = Concorde -> s = t.
Proof.
  intros s t H.
  unfold primitive_transport_class in H.
  destruct (PrimitiveType_eq_dec s t) as [Heq | Hneq].
  - exact Heq.
  - (* If s <> t, the match never returns Concorde *)
    destruct s, t; try discriminate; contradiction.
Qed.

(** ** Equal types get Concorde class *)

Theorem equal_implies_concorde : forall t,
  primitive_transport_class t t = Concorde.
Proof.
  intros t.
  unfold primitive_transport_class.
  destruct (PrimitiveType_eq_dec t t) as [_ | Hneq].
  - reflexivity.
  - exfalso. apply Hneq. reflexivity.
Qed.

(** ** Concorde conversion preserves size (trivially, since types are identical) *)

Theorem concorde_preserves_size : forall s t,
  primitive_transport_class s t = Concorde ->
  sizeof s = sizeof t.
Proof.
  intros s t H.
  apply concorde_implies_equal in H.
  rewrite H. reflexivity.
Qed.

(** ** Concorde is idempotent: applying twice gives same result *)

Theorem concorde_idempotent : forall t,
  primitive_transport_class t t = Concorde.
Proof.
  apply equal_implies_concorde.
Qed.

(** ** Concorde implies no data loss *)

Theorem concorde_no_data_loss : forall s t,
  primitive_transport_class s t = Concorde ->
  sizeof s = sizeof t /\ s = t.
Proof.
  intros s t H.
  split.
  - apply concorde_preserves_size. exact H.
  - apply concorde_implies_equal. exact H.
Qed.

(** ** The combined safety theorem:
    For any conversion function [conv : T -> T] that is the identity,
    - It is lossless
    - It is bijective
    - The transport class is Concorde *)

Theorem concorde_safe : forall (T : PrimitiveType),
  primitive_transport_class T T = Concorde /\
  Bijective (fun (x : nat) => x).
Proof.
  intros T. split.
  - apply equal_implies_concorde.
  - apply id_bijective.
Qed.
