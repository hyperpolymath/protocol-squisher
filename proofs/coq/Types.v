(* SPDX-License-Identifier: PMPL-1.0-or-later *)
(* SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell *)

(** * Core type definitions for Protocol Squisher formal proofs.

    Mirrors the Agda [Types.agda] definitions:
    - Primitive types with size functions
    - Transport classes (Concorde, Business, Economy, Wheelbarrow)
    - Safe widening and narrowing relations
    - Transport class ordering and composition *)

Require Import Arith.
Require Import Lia.

(** ** Primitive Types *)

Inductive PrimitiveType : Set :=
  | I8 | I16 | I32 | I64 | I128
  | U8 | U16 | U32 | U64 | U128
  | F32 | F64
  | Bool
  | String.

(** ** Transport Classes

    Ordered from best (Concorde) to worst (Wheelbarrow).
    - Concorde: 100% fidelity, 0% overhead (identical types)
    - Business: 98% fidelity, 5% overhead (safe widening)
    - Economy: 80% fidelity, 25% overhead (lossy but documented)
    - Wheelbarrow: 50% fidelity, 80% overhead (JSON fallback) *)

Inductive TransportClass : Set :=
  | Concorde
  | Business
  | Economy
  | Wheelbarrow.

(** ** Size function (in bits) *)

Definition sizeof (t : PrimitiveType) : nat :=
  match t with
  | I8 => 8 | I16 => 16 | I32 => 32 | I64 => 64 | I128 => 128
  | U8 => 8 | U16 => 16 | U32 => 32 | U64 => 64 | U128 => 128
  | F32 => 32 | F64 => 64
  | Bool => 1
  | String => 0  (* Variable size *)
  end.

(** ** Signedness *)

Inductive Signedness : Set :=
  | Signed | Unsigned | Neither.

Definition signedness (t : PrimitiveType) : Signedness :=
  match t with
  | I8 | I16 | I32 | I64 | I128 => Signed
  | U8 | U16 | U32 | U64 | U128 => Unsigned
  | F32 | F64 | Bool | String => Neither
  end.

(** ** Safe widening relation

    [safe_widening s t] holds when type [s] can be losslessly widened
    to type [t] (same signedness, target is strictly larger). *)

Inductive safe_widening : PrimitiveType -> PrimitiveType -> Prop :=
  (* Signed integer widening *)
  | sw_I8_I16 : safe_widening I8 I16
  | sw_I8_I32 : safe_widening I8 I32
  | sw_I8_I64 : safe_widening I8 I64
  | sw_I8_I128 : safe_widening I8 I128
  | sw_I16_I32 : safe_widening I16 I32
  | sw_I16_I64 : safe_widening I16 I64
  | sw_I16_I128 : safe_widening I16 I128
  | sw_I32_I64 : safe_widening I32 I64
  | sw_I32_I128 : safe_widening I32 I128
  | sw_I64_I128 : safe_widening I64 I128
  (* Unsigned integer widening *)
  | sw_U8_U16 : safe_widening U8 U16
  | sw_U8_U32 : safe_widening U8 U32
  | sw_U8_U64 : safe_widening U8 U64
  | sw_U8_U128 : safe_widening U8 U128
  | sw_U16_U32 : safe_widening U16 U32
  | sw_U16_U64 : safe_widening U16 U64
  | sw_U16_U128 : safe_widening U16 U128
  | sw_U32_U64 : safe_widening U32 U64
  | sw_U32_U128 : safe_widening U32 U128
  | sw_U64_U128 : safe_widening U64 U128
  (* Float widening *)
  | sw_F32_F64 : safe_widening F32 F64.

(** ** Transport class ordering *)

Definition transport_class_rank (c : TransportClass) : nat :=
  match c with
  | Concorde => 0
  | Business => 1
  | Economy => 2
  | Wheelbarrow => 3
  end.

Definition tc_le (a b : TransportClass) : Prop :=
  transport_class_rank a <= transport_class_rank b.

(** ** Worst (maximum) transport class *)

Definition worst_class (a b : TransportClass) : TransportClass :=
  match a, b with
  | Wheelbarrow, _ => Wheelbarrow
  | _, Wheelbarrow => Wheelbarrow
  | Economy, _ => Economy
  | _, Economy => Economy
  | Business, _ => Business
  | _, Business => Business
  | Concorde, Concorde => Concorde
  end.

(** ** Primitive type equality is decidable *)

Definition PrimitiveType_eq_dec : forall (t1 t2 : PrimitiveType), {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality.
Defined.

(** ** Transport class assignment for primitive type pairs *)

Definition primitive_transport_class (s t : PrimitiveType) : TransportClass :=
  if PrimitiveType_eq_dec s t then Concorde
  else match s, t with
  (* Safe widening cases → Business *)
  | I8, I16 | I8, I32 | I8, I64 | I8, I128 => Business
  | I16, I32 | I16, I64 | I16, I128 => Business
  | I32, I64 | I32, I128 => Business
  | I64, I128 => Business
  | U8, U16 | U8, U32 | U8, U64 | U8, U128 => Business
  | U16, U32 | U16, U64 | U16, U128 => Business
  | U32, U64 | U32, U128 => Business
  | U64, U128 => Business
  | F32, F64 => Business
  (* Everything else → Wheelbarrow *)
  | _, _ => Wheelbarrow
  end.

(** ** Key lemma: safe widening implies source is strictly smaller *)

Lemma safe_widening_size : forall s t,
  safe_widening s t -> sizeof s < sizeof t.
Proof.
  intros s t H; destruct H; simpl; lia.
Qed.

(** ** Worst class is commutative *)

Lemma worst_class_comm : forall a b,
  worst_class a b = worst_class b a.
Proof.
  intros a b; destruct a, b; reflexivity.
Qed.

(** ** Worst class is idempotent *)

Lemma worst_class_idem : forall a,
  worst_class a a = a.
Proof.
  intros a; destruct a; reflexivity.
Qed.

(** ** Concorde is identity for worst_class *)

Lemma worst_class_concorde_left : forall c,
  worst_class Concorde c = c.
Proof.
  intros c; destruct c; reflexivity.
Qed.

(** ** Wheelbarrow is absorbing for worst_class *)

Lemma worst_class_wheelbarrow_left : forall c,
  worst_class Wheelbarrow c = Wheelbarrow.
Proof.
  intros c; destruct c; reflexivity.
Qed.
