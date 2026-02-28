(* SPDX-License-Identifier: PMPL-1.0-or-later *)
(* SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell *)

theory WheelbarrowNecessity
  imports Types
begin

section \<open>Wheelbarrow Necessity Theorem\<close>

text \<open>
  This theory formalizes the WheelbarrowNecessity proof from the Agda
  development. The core claim is:

  For incompatible primitive type pairs (different signedness, or types
  that cannot be widened), no lossless transport class exists except
  Wheelbarrow (JSON fallback).

  In other words: when types don't match and safe widening doesn't apply,
  Wheelbarrow is the ONLY correct classification.
\<close>

subsection \<open>Incompatible pairs always get Wheelbarrow\<close>

text \<open>
  If two types are neither equal nor in a safe widening relationship,
  they must be classified as Wheelbarrow.
\<close>

theorem wheelbarrow_for_incompatible:
  assumes "s \<noteq> t"
  assumes "\<not> safe_widening s t"
  shows "transport_class s t = Wheelbarrow"
  using assms by simp

subsection \<open>Specific incompatible pairs\<close>

text \<open>
  Concrete examples showing that cross-signedness and cross-category
  conversions always produce Wheelbarrow.
\<close>

lemma signed_to_unsigned_wheelbarrow:
  "transport_class I32 U32 = Wheelbarrow"
  by (simp add: safe_widening.simps)

lemma unsigned_to_signed_wheelbarrow:
  "transport_class U64 I64 = Wheelbarrow"
  by (simp add: safe_widening.simps)

lemma int_to_float_wheelbarrow:
  "transport_class I32 F32 = Wheelbarrow"
  by (simp add: safe_widening.simps)

lemma float_to_int_wheelbarrow:
  "transport_class F64 I64 = Wheelbarrow"
  by (simp add: safe_widening.simps)

lemma string_to_int_wheelbarrow:
  "transport_class String I32 = Wheelbarrow"
  by (simp add: safe_widening.simps)

lemma bool_to_int_wheelbarrow:
  "transport_class Bool I8 = Wheelbarrow"
  by (simp add: safe_widening.simps)

subsection \<open>Narrowing requires Wheelbarrow\<close>

text \<open>
  If safe_widening holds in one direction (s \<rightarrow> t), the reverse
  direction (t \<rightarrow> s) is Wheelbarrow because narrowing cannot be lossless.
\<close>

theorem narrowing_is_wheelbarrow:
  assumes "safe_widening s t"
  assumes "s \<noteq> t"
  shows "transport_class t s = Wheelbarrow"
proof -
  from assms have "t \<noteq> s" by auto
  moreover have "\<not> safe_widening t s"
    using assms by (cases rule: safe_widening.cases) (auto intro: safe_widening.intros)
  ultimately show ?thesis by simp
qed

subsection \<open>Wheelbarrow is the worst class\<close>

text \<open>
  Wheelbarrow absorbs all other classes under worst_class composition.
  This means once any component of a compound type requires Wheelbarrow,
  the entire compound does too.
\<close>

theorem wheelbarrow_absorbs:
  "worst_class Wheelbarrow c = Wheelbarrow"
  by (cases c) auto

theorem wheelbarrow_absorbs_right:
  "worst_class c Wheelbarrow = Wheelbarrow"
  by (cases c) auto

subsection \<open>Necessity summary\<close>

text \<open>
  The Wheelbarrow class is necessary because:
  1. Some type pairs are genuinely incompatible (no lossless conversion exists)
  2. The system must still transport data (the "If It Compiles, It Carries" invariant)
  3. JSON serialization is the universal fallback that satisfies both constraints

  Without Wheelbarrow, the system would either:
  - Refuse to handle incompatible types (violating the invariant), or
  - Silently lose data (violating safety guarantees)
\<close>

end
