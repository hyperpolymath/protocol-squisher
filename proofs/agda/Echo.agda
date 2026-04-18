-- SPDX-License-Identifier: PMPL-1.0-or-later
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

{-# OPTIONS --safe --without-K #-}

module Echo where

open import Level using (Level; _⊔_)
open import Function.Base using (_∘_; id)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

-- Echo_f(y) := Σ (x : A) , (f x ≡ y)
Echo : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) → B → Set (a ⊔ b)
Echo {A = A} f y = Σ A (λ x → f x ≡ y)

-- Introduction into own fiber.
echo-intro : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (x : A) → Echo f (f x)
echo-intro f x = x , refl

-- Morphisms in the slice over fixed codomain B.
MapOver :
  ∀ {a a' b} {A : Set a} {A' : Set a'} {B : Set b} →
  (f : A → B) → (f' : A' → B) → Set (a ⊔ a' ⊔ b)
MapOver {A = A} {A' = A'} f f' = Σ (A → A') (λ u → ∀ x → f' (u x) ≡ f x)

-- Action on fibers for a map over fixed base B.
map-over :
  ∀ {a a' b} {A : Set a} {A' : Set a'} {B : Set b}
  {f : A → B} {f' : A' → B} →
  MapOver f f' → ∀ {y : B} → Echo f y → Echo f' y
map-over (u , commute) (x , p) = u x , trans (commute x) p

-- Identity law (pointwise on each fiber element).
map-over-id :
  ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {y : B} (e : Echo f y) →
  map-over (id , (λ x → refl)) e ≡ e
map-over-id (x , p) = refl

trans-assoc :
  ∀ {a} {A : Set a} {x y z w : A}
  (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) →
  trans (trans p q) r ≡ trans p (trans q r)
trans-assoc refl q r = refl

-- Composition law (pointwise on each fiber element).
map-over-comp :
  ∀ {a a' a'' b}
  {A : Set a} {A' : Set a'} {A'' : Set a''} {B : Set b}
  {f : A → B} {f' : A' → B} {f'' : A'' → B}
  (u1 : A → A') (c1 : ∀ x → f' (u1 x) ≡ f x)
  (u2 : A' → A'') (c2 : ∀ x → f'' (u2 x) ≡ f' x)
  {y : B} (e : Echo f y) →
  map-over {f = f} {f' = f''}
    (u2 ∘ u1 , (λ x → trans (c2 (u1 x)) (c1 x))) e
  ≡ map-over {f = f'} {f' = f''} (u2 , c2)
      (map-over {f = f} {f' = f'} (u1 , c1) e)
map-over-comp u1 c1 u2 c2 (x , p)
  rewrite trans-assoc (c2 (u1 x)) (c1 x) p = refl

-- Action along a commuting square: f' ∘ u = v ∘ f.
map-square :
  ∀ {a a' b b'}
  {A : Set a} {A' : Set a'} {B : Set b} {B' : Set b'}
  (f : A → B) (f' : A' → B') (u : A → A') (v : B → B')
  (square : ∀ x → f' (u x) ≡ v (f x)) {y : B} →
  Echo f y → Echo f' (v y)
map-square f f' u v square (x , p) = u x , trans (square x) (cong v p)
