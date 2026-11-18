-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

{-# OPTIONS --safe --without-K --cubical-compatible #-}

-- PQ4: Adapter synthesis correctness.
--
-- The adapter synthesis algorithm takes two format schemas and produces
-- an adapter that translates every field from the source schema to the
-- target schema.  What this module proves is narrower (scoped 2026-11-18):
--
--   1. For every field list a SynthesizedAdapter record exists
--      (synthesis-total). Its `adapter` component is a placeholder unit
--      identity adapter, the same for every list. It is NOT derived from
--      the fields, so this does not prove field preservation.
--   2. Every field has a conversion strategy for its transport class
--      (synthesis-preserves-carries). This is per-field classification,
--      not a proof that the adapter moves the field's data.
--   3. Every field's class is ≤ the list's worst class
--      (synthesis-transport-class-correct).
--   4. Schema adapters compose (synthesis-composition, from
--      CarriesInvariant.adapter-composition).
--
-- Open: derive the source and target schemas and the adapter from the
-- field list, and prove that the adapter preserves each field.
--
-- Proof strategy:
--   Fields are modelled as PrimitiveType pairs (src-field, tgt-field).
--   A SynthesizedAdapter is a record bundling the adapter with proofs
--   of 2 and 3.  Synthesis produces the adapter + both proofs by
--   appealing to the already-verified CarriesInvariant theorems.

module AdapterSynthesis where

open import Types
open import CarriesInvariant using
  (Schema; Adapter; mkAdapter; protocol-squisher-invariant;
   ConversionStrategy; transport-class-has-strategy;
   adapter-composition)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤)

-- ─── Field-level transport class ─────────────────────────────────────────────

-- A FieldSpec pairs a source primitive with a target primitive.
record FieldSpec : Set where
  constructor mkField
  field
    src-type : PrimitiveType
    tgt-type : PrimitiveType

-- The transport class of a single field conversion.
field-transport-class : FieldSpec → TransportClass
field-transport-class (mkField s t) = primitive-transport-class s t

-- ─── Schema as a list of fields ──────────────────────────────────────────────

-- We model a schema as a list of field specs.  This is a simplification
-- of the full IR schema (which includes named fields, container types, and
-- optional/required markers) but captures the essential type-safety property.

data FieldList : Set where
  []     : FieldList
  _∷_    : FieldSpec → FieldList → FieldList

-- Membership of a field in a field list.
data _∈F_ (f : FieldSpec) : FieldList → Set where
  here  : ∀ {fs} → f ∈F (f ∷ fs)
  there : ∀ {g fs} → f ∈F fs → f ∈F (g ∷ fs)

-- The overall transport class for a list of fields is the worst per-field class.
fields-transport-class : FieldList → TransportClass
fields-transport-class []       = Concorde       -- no fields: trivially Concorde
fields-transport-class (f ∷ fs) =
  worst-class (field-transport-class f) (fields-transport-class fs)

-- ─── SynthesizedAdapter ──────────────────────────────────────────────────────

-- A SynthesizedAdapter bundles a Schema-level Adapter with proofs that:
--   (a) every source field has a conversion strategy (carries invariant), and
--   (b) the declared transport class is correct.
record SynthesizedAdapter (fields : FieldList) : Set₁ where
  constructor mkSynth
  field
    -- A Schema adapter. Nothing here ties it to `fields`; synthesis-total
    -- fills it with a placeholder unit identity adapter.
    adapter : Σ Schema (λ src → Σ Schema (λ tgt → Adapter src tgt))
    -- Every field has a strategy
    field-strategies : ∀ (f : FieldSpec) →
      f ≡ mkField (FieldSpec.src-type f) (FieldSpec.tgt-type f) →
      ∃ (λ (strategy : ConversionStrategy
              (primitive-transport-class (FieldSpec.src-type f) (FieldSpec.tgt-type f))) →
        ∀ (x : Set) → ∃ (λ (y : Maybe Set) → Set))
    -- Every field of the list has a class ≤ the declared (worst) class.
    -- (Restated 2026-11-18: it quantified over ALL FieldSpecs, which is false
    -- for a field outside the list, e.g. any Wheelbarrow field against [].)
    class-correct : ∀ (f : FieldSpec) → f ∈F fields →
      field-transport-class f ≤TransportClass fields-transport-class fields

-- ─── Synthesis is total ───────────────────────────────────────────────────────

-- LEMMA: Every FieldSpec has a conversion strategy.
-- Proof: apply protocol-squisher-invariant to the field's src/tgt types.
field-has-strategy : ∀ (f : FieldSpec) →
  ∃ (λ (strategy : ConversionStrategy
        (primitive-transport-class (FieldSpec.src-type f) (FieldSpec.tgt-type f))) →
    ∀ (x : Set) → ∃ (λ (y : Maybe Set) → Set))
field-has-strategy (mkField s t) = protocol-squisher-invariant s t

-- LEMMA: The worst-class function is monotone on both arguments.
worst-class-mono-left : ∀ (c₁ c₂ : TransportClass) →
  c₁ ≤TransportClass worst-class c₁ c₂
worst-class-mono-left Concorde Concorde    = Concorde≤Concorde
worst-class-mono-left Concorde Business   = Concorde≤Business
worst-class-mono-left Concorde Economy    = Concorde≤Economy
worst-class-mono-left Concorde Wheelbarrow = Concorde≤Wheelbarrow
worst-class-mono-left Business Concorde   = Business≤Business
worst-class-mono-left Business Business   = Business≤Business
worst-class-mono-left Business Economy    = Business≤Economy
worst-class-mono-left Business Wheelbarrow = Business≤Wheelbarrow
worst-class-mono-left Economy Concorde    = Economy≤Economy
worst-class-mono-left Economy Business   = Economy≤Economy
worst-class-mono-left Economy Economy    = Economy≤Economy
worst-class-mono-left Economy Wheelbarrow = Economy≤Wheelbarrow
worst-class-mono-left Wheelbarrow _      = Wheelbarrow≤Wheelbarrow

worst-class-mono-right : ∀ (c₁ c₂ : TransportClass) →
  c₂ ≤TransportClass worst-class c₁ c₂
worst-class-mono-right Concorde Concorde    = Concorde≤Concorde
worst-class-mono-right Concorde Business   = Business≤Business
worst-class-mono-right Concorde Economy    = Economy≤Economy
worst-class-mono-right Concorde Wheelbarrow = Wheelbarrow≤Wheelbarrow
worst-class-mono-right Business Concorde   = Concorde≤Business
worst-class-mono-right Business Business   = Business≤Business
worst-class-mono-right Business Economy    = Economy≤Economy
worst-class-mono-right Business Wheelbarrow = Wheelbarrow≤Wheelbarrow
worst-class-mono-right Economy Concorde   = Concorde≤Economy
worst-class-mono-right Economy Business   = Business≤Economy
worst-class-mono-right Economy Economy    = Economy≤Economy
worst-class-mono-right Economy Wheelbarrow = Wheelbarrow≤Wheelbarrow
worst-class-mono-right Wheelbarrow Concorde = Concorde≤Wheelbarrow
worst-class-mono-right Wheelbarrow Business = Business≤Wheelbarrow
worst-class-mono-right Wheelbarrow Economy = Economy≤Wheelbarrow
worst-class-mono-right Wheelbarrow Wheelbarrow = Wheelbarrow≤Wheelbarrow

-- LEMMA: every field's class is ≤ the overall fields-transport-class.
field-class-le-overall : ∀ (f : FieldSpec) (fs : FieldList) →
  field-transport-class f ≤TransportClass fields-transport-class (f ∷ fs)
field-class-le-overall f fs =
  worst-class-mono-left (field-transport-class f) (fields-transport-class fs)

-- ≤TransportClass is transitive.
≤TC-trans : ∀ {a b c : TransportClass} →
  a ≤TransportClass b → b ≤TransportClass c → a ≤TransportClass c
≤TC-trans Concorde≤Concorde Concorde≤Concorde = Concorde≤Concorde
≤TC-trans Concorde≤Concorde Concorde≤Business = Concorde≤Business
≤TC-trans Concorde≤Concorde Concorde≤Economy = Concorde≤Economy
≤TC-trans Concorde≤Concorde Concorde≤Wheelbarrow = Concorde≤Wheelbarrow
≤TC-trans Concorde≤Business Business≤Business = Concorde≤Business
≤TC-trans Concorde≤Business Business≤Economy = Concorde≤Economy
≤TC-trans Concorde≤Business Business≤Wheelbarrow = Concorde≤Wheelbarrow
≤TC-trans Concorde≤Economy Economy≤Economy = Concorde≤Economy
≤TC-trans Concorde≤Economy Economy≤Wheelbarrow = Concorde≤Wheelbarrow
≤TC-trans Concorde≤Wheelbarrow Wheelbarrow≤Wheelbarrow = Concorde≤Wheelbarrow
≤TC-trans Business≤Business Business≤Business = Business≤Business
≤TC-trans Business≤Business Business≤Economy = Business≤Economy
≤TC-trans Business≤Business Business≤Wheelbarrow = Business≤Wheelbarrow
≤TC-trans Business≤Economy Economy≤Economy = Business≤Economy
≤TC-trans Business≤Economy Economy≤Wheelbarrow = Business≤Wheelbarrow
≤TC-trans Business≤Wheelbarrow Wheelbarrow≤Wheelbarrow = Business≤Wheelbarrow
≤TC-trans Economy≤Economy Economy≤Economy = Economy≤Economy
≤TC-trans Economy≤Economy Economy≤Wheelbarrow = Economy≤Wheelbarrow
≤TC-trans Economy≤Wheelbarrow Wheelbarrow≤Wheelbarrow = Economy≤Wheelbarrow
≤TC-trans Wheelbarrow≤Wheelbarrow Wheelbarrow≤Wheelbarrow = Wheelbarrow≤Wheelbarrow

-- LEMMA: the class of every field in a list is ≤ the list's overall class.
member-class-le-overall : ∀ {f fs} → f ∈F fs →
  field-transport-class f ≤TransportClass fields-transport-class fs
member-class-le-overall {f} {.f ∷ fs} here =
  worst-class-mono-left (field-transport-class f) (fields-transport-class fs)
member-class-le-overall {f} {g ∷ fs} (there m) =
  ≤TC-trans (member-class-le-overall m)
    (worst-class-mono-right (field-transport-class g) (fields-transport-class fs))

-- THEOREM (PQ4-a): For any field list, a SynthesizedAdapter record exists.
-- The adapter component is a unit identity adapter, identical for every
-- list (including []), so this is NOT a proof of field-preserving synthesis.
synthesis-total : ∀ (fields : FieldList) → SynthesizedAdapter fields
synthesis-total fields = mkSynth
  -- adapter: use the generic Schema-level compilation-implies-transport
  (mkSchema ⊤ (λ _ → ⊤) ,
   mkSchema ⊤ (λ _ → ⊤) ,
   mkAdapter (λ x → just x) (λ x v → x , refl , v))
  -- field-strategies: every field has a strategy via field-has-strategy
  (λ f _ → field-has-strategy f)
  -- class-correct: every field class ≤ overall class
  (λ f m → member-class-le-overall m)
  where
    open import CarriesInvariant using (mkSchema; mkAdapter)

-- ─── Synthesis preserves CarriesInvariant ─────────────────────────────────────

-- THEOREM (PQ4-b): Every field has a conversion strategy for its transport
-- class. This classifies fields; it does not show that the synthesized
-- adapter moves any field's data.
synthesis-preserves-carries : ∀ (fields : FieldList) →
  ∀ (f : FieldSpec) →
  ∃ (λ (strategy : ConversionStrategy
        (primitive-transport-class (FieldSpec.src-type f) (FieldSpec.tgt-type f))) →
    ∀ (x : Set) → ∃ (λ (y : Maybe Set) → Set))
synthesis-preserves-carries fields f = field-has-strategy f

-- ─── Transport class correctness ─────────────────────────────────────────────

-- THEOREM (PQ4-c): The overall transport class of a synthesized adapter is
-- the worst class across all its fields.
synthesis-transport-class-correct : ∀ (fields : FieldList) →
  ∀ (f : FieldSpec) →
  field-transport-class f ≤TransportClass fields-transport-class (f ∷ fields)
synthesis-transport-class-correct fields f = field-class-le-overall f fields

-- ─── Composition ─────────────────────────────────────────────────────────────

-- THEOREM (PQ4-d): Composition of two synthesized adapters is correct.
-- If adapter A→B and B→C are both synthesized (and correct), then
-- the composed adapter A→C exists and carries all data.
--
-- This follows from CarriesInvariant.adapter-composition (already proven).

synthesis-composition : ∀ {A B C : Schema} →
  Adapter A B →
  Adapter B C →
  Adapter A C
synthesis-composition = adapter-composition

-- ─── End-to-end synthesis theorem ────────────────────────────────────────────

-- THEOREM (PQ4-complete): For any source field list there is a
-- SynthesizedAdapter record (PQ4-a) and every field has a conversion
-- strategy (PQ4-b). It does NOT prove that the adapter preserves the
-- fields: the adapter is the placeholder from PQ4-a, and tgt-fields is
-- unused.

synthesis-end-to-end : ∀ (src-fields tgt-fields : FieldList) →
  ∃ (λ (sa : SynthesizedAdapter src-fields) →
    ∀ (f : FieldSpec) →
    ∃ (λ (strategy : ConversionStrategy
          (primitive-transport-class (FieldSpec.src-type f) (FieldSpec.tgt-type f))) →
      ∀ (x : Set) → ∃ (λ (y : Maybe Set) → Set)))
synthesis-end-to-end src-fields tgt-fields =
  synthesis-total src-fields ,
  synthesis-preserves-carries src-fields

-- Summary
-- =======
-- PQ4 is PARTLY proved (scoped 2026-11-18).
--
--   Proved: every field has a strategy; every field's class is ≤ the
--   list's worst class; Schema adapters compose; a SynthesizedAdapter
--   record exists for every list.
--   Not proved: that a synthesized adapter preserves the fields. The
--   record's adapter is a placeholder unrelated to the field list.
