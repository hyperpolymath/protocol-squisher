-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

{-# OPTIONS --safe --without-K #-}

module Types where

open import Data.Nat using (ℕ; _≤_; _<_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

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
  Container₁ : (IrType → Container IrType) → IrType → IrType

-- Type equality
_≟Type_ : (t₁ t₂ : PrimitiveType) → Set
t₁ ≟Type t₂ = t₁ ≡ t₂

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

-- Transport class for primitive type pair
primitive-transport-class : PrimitiveType → PrimitiveType → TransportClass
primitive-transport-class s t with s ≟Type t
... | refl = Concorde  -- Identical types → Concorde
primitive-transport-class I8 I16 = Business
primitive-transport-class I8 I32 = Business
primitive-transport-class I8 I64 = Business
primitive-transport-class I8 I128 = Business
primitive-transport-class I16 I32 = Business
primitive-transport-class I16 I64 = Business
primitive-transport-class I16 I128 = Business
primitive-transport-class I32 I64 = Business
primitive-transport-class I32 I128 = Business
primitive-transport-class I64 I128 = Business
primitive-transport-class U8 U16 = Business
primitive-transport-class U8 U32 = Business
primitive-transport-class U8 U64 = Business
primitive-transport-class U8 U128 = Business
primitive-transport-class U16 U32 = Business
primitive-transport-class U16 U64 = Business
primitive-transport-class U16 U128 = Business
primitive-transport-class U32 U64 = Business
primitive-transport-class U32 U128 = Business
primitive-transport-class U64 U128 = Business
primitive-transport-class F32 F64 = Business
primitive-transport-class _ _ = Wheelbarrow  -- Everything else
