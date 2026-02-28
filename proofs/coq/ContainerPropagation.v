(* SPDX-License-Identifier: PMPL-1.0-or-later *)
(* SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell *)

(** * Container Propagation Proofs

    Cross-validates the Agda proof in ContainerPropagation.agda.

    Proves algebraic properties of [worst_class] — the function that
    computes the transport class of composite types (containers) from
    their element types.  These properties guarantee that the optimizer's
    container analysis is correct. *)

Require Import Types.

(** ** Worst-class is associative

    [(worst_class (worst_class a b) c) = worst_class a (worst_class b c)]

    This ensures that nesting containers (e.g., Vec<Map<K,V>>) gives
    the same result regardless of evaluation order. *)

Theorem worst_class_assoc : forall a b c : TransportClass,
  worst_class (worst_class a b) c = worst_class a (worst_class b c).
Proof.
  intros a b c; destruct a, b, c; reflexivity.
Qed.

(** ** Worst-class is commutative

    [worst_class a b = worst_class b a]

    Element order does not affect the container's transport class. *)

Theorem worst_class_comm_full : forall a b : TransportClass,
  worst_class a b = worst_class b a.
Proof.
  intros a b; destruct a, b; reflexivity.
Qed.

(** ** Worst-class is idempotent

    [worst_class a a = a]

    A container of identical-class elements has the same class. *)

Theorem worst_class_idem_full : forall a : TransportClass,
  worst_class a a = a.
Proof.
  intros a; destruct a; reflexivity.
Qed.

(** ** Wheelbarrow is absorbing (left)

    [worst_class Wheelbarrow c = Wheelbarrow]

    If any element is Wheelbarrow, the whole container is Wheelbarrow.
    Cross-validates Agda's [worst-class-wheelbarrow]. *)

Theorem wheelbarrow_absorbing_left : forall c : TransportClass,
  worst_class Wheelbarrow c = Wheelbarrow.
Proof.
  intros c; destruct c; reflexivity.
Qed.

(** ** Wheelbarrow is absorbing (right)

    [worst_class c Wheelbarrow = Wheelbarrow]

    Follows from commutativity + left absorption, but proved
    independently by case analysis for cross-validation. *)

Theorem wheelbarrow_absorbing_right : forall c : TransportClass,
  worst_class c Wheelbarrow = Wheelbarrow.
Proof.
  intros c; destruct c; reflexivity.
Qed.

(** ** Concorde is identity (left)

    [worst_class Concorde c = c]

    A Concorde-class element does not degrade the container.
    Cross-validates Agda's [worst-class-concorde]. *)

Theorem concorde_identity_left : forall c : TransportClass,
  worst_class Concorde c = c.
Proof.
  intros c; destruct c; reflexivity.
Qed.

(** ** Concorde is identity (right)

    [worst_class c Concorde = c]

    Follows from commutativity + left identity, proved independently. *)

Theorem concorde_identity_right : forall c : TransportClass,
  worst_class c Concorde = c.
Proof.
  intros c; destruct c; reflexivity.
Qed.

(** ** Worst-class forms a bounded join-semilattice

    Concorde is the bottom (identity) and Wheelbarrow is the top
    (absorbing element).  This means worst_class computes the join
    (least upper bound) of two transport classes. *)

Theorem worst_class_bounded :
  (forall c, worst_class Concorde c = c) /\
  (forall c, worst_class c Wheelbarrow = Wheelbarrow).
Proof.
  split.
  - exact concorde_identity_left.
  - exact wheelbarrow_absorbing_right.
Qed.

(** ** Container Wheelbarrow propagation

    If the element class is Wheelbarrow, the container class
    (worst_class element_class Business) is also Wheelbarrow.
    This proves that Wheelbarrow-class elements "infect" their
    containers. *)

Theorem container_wheelbarrow_propagation :
  worst_class Wheelbarrow Business = Wheelbarrow.
Proof.
  reflexivity.
Qed.

(** ** Transport class ordering is total

    The rank function induces a total order.  We prove that for
    any two classes, one is [<=] the other. *)

Theorem tc_le_total : forall a b : TransportClass,
  transport_class_rank a <= transport_class_rank b \/
  transport_class_rank b <= transport_class_rank a.
Proof.
  intros a b; destruct a, b; simpl; lia.
Qed.

(** ** Worst_class computes the maximum rank

    [transport_class_rank (worst_class a b) =
     max (transport_class_rank a) (transport_class_rank b)] *)

Theorem worst_class_is_max : forall a b : TransportClass,
  transport_class_rank (worst_class a b) =
  Nat.max (transport_class_rank a) (transport_class_rank b).
Proof.
  intros a b; destruct a, b; simpl; reflexivity.
Qed.

(** SUMMARY:
    ========
    Container propagation proofs (cross-validating Agda):
      1. worst_class_assoc — associativity
      2. worst_class_comm_full — commutativity
      3. worst_class_idem_full — idempotency
      4. wheelbarrow_absorbing_{left,right} — Wheelbarrow absorbs
      5. concorde_identity_{left,right} — Concorde is identity
      6. worst_class_bounded — bounded join-semilattice
      7. container_wheelbarrow_propagation — Wheelbarrow infects containers
      8. tc_le_total — transport class ordering is total
      9. worst_class_is_max — worst_class = max in the ordering

    No Admitted. Cross-validates Agda ContainerPropagation.agda. *)
