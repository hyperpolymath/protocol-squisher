-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

{-# OPTIONS --safe --without-K --cubical-compatible #-}

module Types where

open import Data.Nat using (ℕ; _≤_; _<_)
import Data.Nat as ℕ
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (map′)
open import Data.Empty using (⊥)

-- Primitive types in protocol-squisher IR
data PrimitiveType : Set where
  I8 I16 I32 I64 I128 : PrimitiveType
  U8 U16 U32 U64 U128 : PrimitiveType
  F32 F64 : PrimitiveType
  Bool : PrimitiveType
  String : PrimitiveType

-- Transport classes
data TransportClass : Set where
  Concorde : TransportClass      -- 100% fidelity, 0% overhead
  Business : TransportClass      -- 98% fidelity, 5% overhead
  Economy : TransportClass       -- 80% fidelity, 25% overhead
  Wheelbarrow : TransportClass   -- 50% fidelity, 80% overhead

-- Size in bits for each primitive type
sizeof : PrimitiveType → ℕ
sizeof I8 = 8
sizeof I16 = 16
sizeof I32 = 32
sizeof I64 = 64
sizeof I128 = 128
sizeof U8 = 8
sizeof U16 = 16
sizeof U32 = 32
sizeof U64 = 64
sizeof U128 = 128
sizeof F32 = 32
sizeof F64 = 64
sizeof Bool = 1
sizeof String = 0  -- Variable size, represented as 0

-- Signedness
data Signedness : Set where
  Signed Unsigned Neither : Signedness

signedness : PrimitiveType → Signedness
signedness I8 = Signed
signedness I16 = Signed
signedness I32 = Signed
signedness I64 = Signed
signedness I128 = Signed
signedness U8 = Unsigned
signedness U16 = Unsigned
signedness U32 = Unsigned
signedness U64 = Unsigned
signedness U128 = Unsigned
signedness F32 = Neither
signedness F64 = Neither
signedness Bool = Neither
signedness String = Neither

-- Container types
data Container (A : Set) : Set where
  Option : A → Container A
  Vec : A → Container A
  Map : A → A → Container A
  Tuple : A → A → Container A

-- IR Type (simplified)
data IrType : Set where
  Primitive : PrimitiveType → IrType
  Container₁ : Container IrType → IrType

-- Decidable equality on PrimitiveType, via an injective index into ℕ.
-- pt-index has a left inverse (pt-from), so equal indices mean equal types.
pt-index : PrimitiveType → ℕ
pt-index I8 = 0
pt-index I16 = 1
pt-index I32 = 2
pt-index I64 = 3
pt-index I128 = 4
pt-index U8 = 5
pt-index U16 = 6
pt-index U32 = 7
pt-index U64 = 8
pt-index U128 = 9
pt-index F32 = 10
pt-index F64 = 11
pt-index Bool = 12
pt-index String = 13

pt-from : ℕ → PrimitiveType
pt-from 0 = I8
pt-from 1 = I16
pt-from 2 = I32
pt-from 3 = I64
pt-from 4 = I128
pt-from 5 = U8
pt-from 6 = U16
pt-from 7 = U32
pt-from 8 = U64
pt-from 9 = U128
pt-from 10 = F32
pt-from 11 = F64
pt-from 12 = Bool
pt-from _ = String

pt-from-index : ∀ t → pt-from (pt-index t) ≡ t
pt-from-index I8 = refl
pt-from-index I16 = refl
pt-from-index I32 = refl
pt-from-index I64 = refl
pt-from-index I128 = refl
pt-from-index U8 = refl
pt-from-index U16 = refl
pt-from-index U32 = refl
pt-from-index U64 = refl
pt-from-index U128 = refl
pt-from-index F32 = refl
pt-from-index F64 = refl
pt-from-index Bool = refl
pt-from-index String = refl

pt-index-injective : ∀ {s t} → pt-index s ≡ pt-index t → s ≡ t
pt-index-injective {s} {t} p =
  trans (sym (pt-from-index s)) (trans (cong pt-from p) (pt-from-index t))

-- Type equality is decidable.
_≟Type_ : (t₁ t₂ : PrimitiveType) → Dec (t₁ ≡ t₂)
s ≟Type t = map′ pt-index-injective (cong pt-index) (pt-index s ℕ.≟ pt-index t)

-- Safe widening predicate
data SafeWidening : PrimitiveType → PrimitiveType → Set where
  -- Signed integer widening
  I8→I16 : SafeWidening I8 I16
  I8→I32 : SafeWidening I8 I32
  I8→I64 : SafeWidening I8 I64
  I8→I128 : SafeWidening I8 I128
  I16→I32 : SafeWidening I16 I32
  I16→I64 : SafeWidening I16 I64
  I16→I128 : SafeWidening I16 I128
  I32→I64 : SafeWidening I32 I64
  I32→I128 : SafeWidening I32 I128
  I64→I128 : SafeWidening I64 I128

  -- Unsigned integer widening
  U8→U16 : SafeWidening U8 U16
  U8→U32 : SafeWidening U8 U32
  U8→U64 : SafeWidening U8 U64
  U8→U128 : SafeWidening U8 U128
  U16→U32 : SafeWidening U16 U32
  U16→U64 : SafeWidening U16 U64
  U16→U128 : SafeWidening U16 U128
  U32→U64 : SafeWidening U32 U64
  U32→U128 : SafeWidening U32 U128
  U64→U128 : SafeWidening U64 U128

  -- Float widening
  F32→F64 : SafeWidening F32 F64

-- Narrowing predicate (inverse of widening)
data Narrowing : PrimitiveType → PrimitiveType → Set where
  narrow : ∀ {s t} → SafeWidening t s → Narrowing s t

-- Transport class ordering (better classes are "less than")
data _≤TransportClass_ : TransportClass → TransportClass → Set where
  Concorde≤Concorde : Concorde ≤TransportClass Concorde
  Concorde≤Business : Concorde ≤TransportClass Business
  Concorde≤Economy : Concorde ≤TransportClass Economy
  Concorde≤Wheelbarrow : Concorde ≤TransportClass Wheelbarrow
  Business≤Business : Business ≤TransportClass Business
  Business≤Economy : Business ≤TransportClass Economy
  Business≤Wheelbarrow : Business ≤TransportClass Wheelbarrow
  Economy≤Economy : Economy ≤TransportClass Economy
  Economy≤Wheelbarrow : Economy ≤TransportClass Wheelbarrow
  Wheelbarrow≤Wheelbarrow : Wheelbarrow ≤TransportClass Wheelbarrow

-- Worst transport class (max in ordering)
worst-class : TransportClass → TransportClass → TransportClass
worst-class Concorde c = c
worst-class Business Concorde = Business
worst-class Business c = c
worst-class Economy Concorde = Economy
worst-class Economy Business = Economy
worst-class Economy c = c
worst-class Wheelbarrow _ = Wheelbarrow

-- The safe-widening table: a SafeWidening witness for exactly the 21
-- widening pairs, nothing for every other pair.
find-widening : (s t : PrimitiveType) → Maybe (SafeWidening s t)
find-widening I8 I16 = just I8→I16
find-widening I8 I32 = just I8→I32
find-widening I8 I64 = just I8→I64
find-widening I8 I128 = just I8→I128
find-widening I16 I32 = just I16→I32
find-widening I16 I64 = just I16→I64
find-widening I16 I128 = just I16→I128
find-widening I32 I64 = just I32→I64
find-widening I32 I128 = just I32→I128
find-widening I64 I128 = just I64→I128
find-widening U8 U16 = just U8→U16
find-widening U8 U32 = just U8→U32
find-widening U8 U64 = just U8→U64
find-widening U8 U128 = just U8→U128
find-widening U16 U32 = just U16→U32
find-widening U16 U64 = just U16→U64
find-widening U16 U128 = just U16→U128
find-widening U32 U64 = just U32→U64
find-widening U32 U128 = just U32→U128
find-widening U64 U128 = just U64→U128
find-widening F32 F64 = just F32→F64
find-widening _ _ = nothing

-- Transport class for a primitive type pair:
-- identical types → Concorde; a safe widening → Business; else Wheelbarrow.
widening-class : ∀ {s t} → Maybe (SafeWidening s t) → TransportClass
widening-class (just _) = Business
widening-class nothing = Wheelbarrow

primitive-transport-class : PrimitiveType → PrimitiveType → TransportClass
primitive-transport-class s t with s ≟Type t
... | yes _ = Concorde
... | no _ = widening-class (find-widening s t)

-- The widening table never yields Concorde.
widening-class-not-concorde : ∀ {s t} (w : Maybe (SafeWidening s t)) →
  widening-class w ≡ Concorde → ⊥
widening-class-not-concorde (just _) ()
widening-class-not-concorde nothing ()
