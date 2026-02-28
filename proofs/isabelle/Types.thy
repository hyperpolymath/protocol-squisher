(* SPDX-License-Identifier: PMPL-1.0-or-later *)
(* SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell *)

theory Types
  imports Main
begin

section \<open>Primitive Types\<close>

text \<open>
  Core type definitions for Protocol Squisher formal proofs.
  Mirrors the Agda Types.agda definitions.
\<close>

datatype PrimitiveType =
    I8 | I16 | I32 | I64 | I128
  | U8 | U16 | U32 | U64 | U128
  | F32 | F64
  | Bool
  | String

section \<open>Transport Classes\<close>

datatype TransportClass =
    Concorde      \<comment> \<open>100% fidelity, 0% overhead\<close>
  | Business      \<comment> \<open>98% fidelity, 5% overhead\<close>
  | Economy       \<comment> \<open>80% fidelity, 25% overhead\<close>
  | Wheelbarrow   \<comment> \<open>50% fidelity, 80% overhead\<close>

section \<open>Size Function\<close>

fun sizeof :: "PrimitiveType \<Rightarrow> nat" where
  "sizeof I8 = 8" |
  "sizeof I16 = 16" |
  "sizeof I32 = 32" |
  "sizeof I64 = 64" |
  "sizeof I128 = 128" |
  "sizeof U8 = 8" |
  "sizeof U16 = 16" |
  "sizeof U32 = 32" |
  "sizeof U64 = 64" |
  "sizeof U128 = 128" |
  "sizeof F32 = 32" |
  "sizeof F64 = 64" |
  "sizeof Bool = 1" |
  "sizeof String = 0"

section \<open>Safe Widening\<close>

inductive safe_widening :: "PrimitiveType \<Rightarrow> PrimitiveType \<Rightarrow> bool" where
  "safe_widening I8 I16" |
  "safe_widening I8 I32" |
  "safe_widening I8 I64" |
  "safe_widening I8 I128" |
  "safe_widening I16 I32" |
  "safe_widening I16 I64" |
  "safe_widening I16 I128" |
  "safe_widening I32 I64" |
  "safe_widening I32 I128" |
  "safe_widening I64 I128" |
  "safe_widening U8 U16" |
  "safe_widening U8 U32" |
  "safe_widening U8 U64" |
  "safe_widening U8 U128" |
  "safe_widening U16 U32" |
  "safe_widening U16 U64" |
  "safe_widening U16 U128" |
  "safe_widening U32 U64" |
  "safe_widening U32 U128" |
  "safe_widening U64 U128" |
  "safe_widening F32 F64"

section \<open>Transport Class Assignment\<close>

fun transport_class :: "PrimitiveType \<Rightarrow> PrimitiveType \<Rightarrow> TransportClass" where
  "transport_class s t = (if s = t then Concorde
    else if safe_widening s t then Business
    else Wheelbarrow)"

section \<open>Worst Class\<close>

fun worst_class :: "TransportClass \<Rightarrow> TransportClass \<Rightarrow> TransportClass" where
  "worst_class Concorde c = c" |
  "worst_class c Concorde = c" |
  "worst_class Wheelbarrow _ = Wheelbarrow" |
  "worst_class _ Wheelbarrow = Wheelbarrow" |
  "worst_class Economy _ = Economy" |
  "worst_class _ Economy = Economy" |
  "worst_class Business Business = Business"

section \<open>Basic Properties\<close>

lemma worst_class_idem: "worst_class c c = c"
  by (cases c) auto

lemma worst_class_concorde_id: "worst_class Concorde c = c"
  by (cases c) auto

lemma worst_class_wheelbarrow_absorb: "worst_class Wheelbarrow c = Wheelbarrow"
  by (cases c) auto

lemma transport_reflexive: "transport_class t t = Concorde"
  by simp

end
