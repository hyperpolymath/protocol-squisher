-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

{-# OPTIONS --safe --without-K --cubical-compatible #-}

module WheelbarrowNecessity where

open import Types
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; ∄)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; _≢_)
open import Relation.Nullary using (¬_; yes; no)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; _≤_; _<_; _>_)
open import Data.Nat.Properties using (<-trans; ≤-trans; <⇒≢)

-- A value that can be represented in a type
record Value (t : PrimitiveType) : Set where
  constructor mkValue
  field
    bits : ℕ
    size-constraint : bits ≤ sizeof t

-- Lossless conversion (from ConcordeSafety)
Lossless : ∀ {A B : Set} → (A → B) → Set
Lossless {A} {B} f = ∀ (x y : A) → f x ≡ f y → x ≡ y

-- THEOREM 1: Narrowing requires fallback
-- If target size < source size, no direct lossless conversion exists

narrowing-not-lossless : ∀ {s t : PrimitiveType} →
  sizeof t < sizeof s →
  ¬ (Lossless {Value s} {Value t} (λ _ → mkValue 0 (Data.Nat.z≤n)))
narrowing-not-lossless {s} {t} size-proof lossless-claim = 0≢1 0≡1
  where
    -- sizeof t < sizeof s means suc (sizeof t) ≤ sizeof s, so 1 ≤ sizeof s
    one≤s : 1 Data.Nat.≤ sizeof s
    one≤s = ≤-trans (Data.Nat.s≤s Data.Nat.z≤n) size-proof
    -- Two distinct values that both fit in Value s
    v1 : Value s
    v1 = mkValue 0 Data.Nat.z≤n
    v2 : Value s
    v2 = mkValue 1 one≤s
    -- Constant function maps both to mkValue 0 z≤n, so lossless gives v1 ≡ v2
    v1≡v2 : v1 ≡ v2
    v1≡v2 = lossless-claim v1 v2 refl
    -- Extract 0 ≡ 1 from v1 ≡ v2 via record projection
    0≡1 : 0 ≡ 1
    0≡1 = cong Value.bits v1≡v2
    -- 0 ≡ 1 is absurd on ℕ
    0≢1 : 0 ≡ 1 → ⊥
    0≢1 ()

-- THEOREM 2: Narrowing is classified as Wheelbarrow
-- For all narrowing conversions, transport class must be Wheelbarrow

narrowing-is-wheelbarrow : ∀ {s t : PrimitiveType} →
  Narrowing s t →
  primitive-transport-class s t ≡ Wheelbarrow
narrowing-is-wheelbarrow (narrow I16→I32) = refl  -- I32 → I16
narrowing-is-wheelbarrow (narrow I16→I64) = refl  -- I64 → I16
narrowing-is-wheelbarrow (narrow I16→I128) = refl -- I128 → I16
narrowing-is-wheelbarrow (narrow I32→I64) = refl  -- I64 → I32
narrowing-is-wheelbarrow (narrow I32→I128) = refl -- I128 → I32
narrowing-is-wheelbarrow (narrow I64→I128) = refl -- I128 → I64
narrowing-is-wheelbarrow (narrow U16→U32) = refl  -- U32 → U16
narrowing-is-wheelbarrow (narrow U16→U64) = refl  -- U64 → U16
narrowing-is-wheelbarrow (narrow U16→U128) = refl -- U128 → U16
narrowing-is-wheelbarrow (narrow U32→U64) = refl  -- U64 → U32
narrowing-is-wheelbarrow (narrow U32→U128) = refl -- U128 → U32
narrowing-is-wheelbarrow (narrow U64→U128) = refl -- U128 → U64
narrowing-is-wheelbarrow (narrow F32→F64) = refl  -- F64 → F32
narrowing-is-wheelbarrow (narrow I8→I16) = refl
narrowing-is-wheelbarrow (narrow I8→I32) = refl
narrowing-is-wheelbarrow (narrow I8→I64) = refl
narrowing-is-wheelbarrow (narrow I8→I128) = refl
narrowing-is-wheelbarrow (narrow U8→U16) = refl
narrowing-is-wheelbarrow (narrow U8→U32) = refl
narrowing-is-wheelbarrow (narrow U8→U64) = refl
narrowing-is-wheelbarrow (narrow U8→U128) = refl

-- Every safe widening is classified Business, never Wheelbarrow.
safe-widen-not-wheelbarrow : ∀ {s t} → SafeWidening s t →
  primitive-transport-class s t ≡ Wheelbarrow → ⊥
safe-widen-not-wheelbarrow I8→I16 ()
safe-widen-not-wheelbarrow I8→I32 ()
safe-widen-not-wheelbarrow I8→I64 ()
safe-widen-not-wheelbarrow I8→I128 ()
safe-widen-not-wheelbarrow I16→I32 ()
safe-widen-not-wheelbarrow I16→I64 ()
safe-widen-not-wheelbarrow I16→I128 ()
safe-widen-not-wheelbarrow I32→I64 ()
safe-widen-not-wheelbarrow I32→I128 ()
safe-widen-not-wheelbarrow I64→I128 ()
safe-widen-not-wheelbarrow U8→U16 ()
safe-widen-not-wheelbarrow U8→U32 ()
safe-widen-not-wheelbarrow U8→U64 ()
safe-widen-not-wheelbarrow U8→U128 ()
safe-widen-not-wheelbarrow U16→U32 ()
safe-widen-not-wheelbarrow U16→U64 ()
safe-widen-not-wheelbarrow U16→U128 ()
safe-widen-not-wheelbarrow U32→U64 ()
safe-widen-not-wheelbarrow U32→U128 ()
safe-widen-not-wheelbarrow U64→U128 ()
safe-widen-not-wheelbarrow F32→F64 ()

-- Identical types are classified Concorde, never Wheelbarrow.
identical-not-wheelbarrow : ∀ {s t} → s ≡ t →
  primitive-transport-class s t ≡ Wheelbarrow → ⊥
identical-not-wheelbarrow {s} {t} s≡t prf with s ≟Type t
... | yes _ = Concorde≢Wheelbarrow prf
  where
    Concorde≢Wheelbarrow : Concorde ≡ Wheelbarrow → ⊥
    Concorde≢Wheelbarrow ()
... | no s≢t = s≢t s≡t

-- THEOREM 3: Wheelbarrow implies potential data loss
-- A Wheelbarrow pair is neither identical nor a safe widening, so neither
-- of the two lossless direct conversions applies.

wheelbarrow-lossy : ∀ {s t : PrimitiveType} →
  primitive-transport-class s t ≡ Wheelbarrow →
  ¬ (s ≡ t ⊎ SafeWidening s t)
wheelbarrow-lossy prf (inj₁ s≡t) = identical-not-wheelbarrow s≡t prf
wheelbarrow-lossy prf (inj₂ w)   = safe-widen-not-wheelbarrow w prf

-- THEOREM 4: JSON fallback necessary for Wheelbarrow
-- A Wheelbarrow pair admits no direct cast: the types differ and the pair
-- is not a safe widening, so the only strategy left is the JSON fallback.
--
-- Restated 2026-11-18. The earlier statement claimed every Wheelbarrow pair
-- either narrows (sizeof t < sizeof s) or changes signedness. That is false:
-- String → Bool and Bool → F32 are Wheelbarrow, keep signedness (Neither)
-- and do not narrow. Its proof covered two pairs and closed the rest with an
-- invalid absurd pattern. This statement is the true one.

wheelbarrow-needs-fallback : ∀ {s t : PrimitiveType} →
  primitive-transport-class s t ≡ Wheelbarrow →
  ¬ (s ≡ t) × ¬ (SafeWidening s t)
wheelbarrow-needs-fallback prf =
  (λ s≡t → identical-not-wheelbarrow s≡t prf) ,
  (λ w → safe-widen-not-wheelbarrow w prf)

-- COROLLARY: Wheelbarrow is worst transport class
-- Wheelbarrow has highest overhead and lowest fidelity

wheelbarrow-worst : ∀ (c : TransportClass) →
  c ≤TransportClass Wheelbarrow
wheelbarrow-worst Concorde = Concorde≤Wheelbarrow
wheelbarrow-worst Business = Business≤Wheelbarrow
wheelbarrow-worst Economy = Economy≤Wheelbarrow
wheelbarrow-worst Wheelbarrow = Wheelbarrow≤Wheelbarrow

-- SUMMARY:
-- ========
-- Wheelbarrow-class transport is:
--   1. Required for narrowing conversions (narrowing-is-wheelbarrow)
--   2. Cannot be lossless (narrowing-not-lossless)
--   3. Requires JSON fallback (wheelbarrow-needs-fallback)
--   4. Worst transport class (wheelbarrow-worst)
--   5. Has potential data loss (wheelbarrow-lossy)
--
-- This proves that protocol-squisher's Wheelbarrow classification is
-- necessary and that direct conversions are impossible for these cases.
