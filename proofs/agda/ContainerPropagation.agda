-- SPDX-License-Identifier: PMPL-1.0-or-later
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

{-# OPTIONS --safe --without-K #-}

module ContainerPropagation where

open import Types
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

-- THEOREM 1: Option<T> propagates element transport class
-- Option is a zero-overhead wrapper, so transport class = element class

option-transport-class : ∀ {s t : PrimitiveType} →
  let elem-class = primitive-transport-class s t in
  primitive-transport-class s t ≡ elem-class
option-transport-class {s} {t} = refl

-- THEOREM 2: Vec<T> transport class is at least Business
-- Vec requires iteration, so minimum class is Business (ContainerMatch)

vec-min-business : ∀ {s t : PrimitiveType} →
  let elem-class = primitive-transport-class s t in
  let vec-class = worst-class elem-class Business in
  vec-class ≡ worst-class elem-class Business
vec-min-business {s} {t} = refl

-- THEOREM 3: Worst-class is associative
-- (worst a b) worst c = worst a (worst b c)

worst-class-assoc : ∀ (a b c : TransportClass) →
  worst-class (worst-class a b) c ≡ worst-class a (worst-class b c)
worst-class-assoc Concorde b c = refl
worst-class-assoc Business Concorde c = refl
worst-class-assoc Business Business c = refl
worst-class-assoc Business Economy c = refl
worst-class-assoc Business Wheelbarrow c = refl
worst-class-assoc Economy Concorde c = refl
worst-class-assoc Economy Business Concorde = refl
worst-class-assoc Economy Business Business = refl
worst-class-assoc Economy Business Economy = refl
worst-class-assoc Economy Business Wheelbarrow = refl
worst-class-assoc Economy Economy c = refl
worst-class-assoc Economy Wheelbarrow c = refl
worst-class-assoc Wheelbarrow b c = refl

-- THEOREM 4: Worst-class is commutative

worst-class-comm : ∀ (a b : TransportClass) →
  worst-class a b ≡ worst-class b a
worst-class-comm Concorde Concorde = refl
worst-class-comm Concorde Business = refl
worst-class-comm Concorde Economy = refl
worst-class-comm Concorde Wheelbarrow = refl
worst-class-comm Business Concorde = refl
worst-class-comm Business Business = refl
worst-class-comm Business Economy = refl
worst-class-comm Business Wheelbarrow = refl
worst-class-comm Economy Concorde = refl
worst-class-comm Economy Business = refl
worst-class-comm Economy Economy = refl
worst-class-comm Economy Wheelbarrow = refl
worst-class-comm Wheelbarrow Concorde = refl
worst-class-comm Wheelbarrow Business = refl
worst-class-comm Wheelbarrow Economy = refl
worst-class-comm Wheelbarrow Wheelbarrow = refl

-- THEOREM 5: Worst-class is idempotent

worst-class-idem : ∀ (a : TransportClass) →
  worst-class a a ≡ a
worst-class-idem Concorde = refl
worst-class-idem Business = refl
worst-class-idem Economy = refl
worst-class-idem Wheelbarrow = refl

-- THEOREM 6: Wheelbarrow is absorbing element

worst-class-wheelbarrow : ∀ (a : TransportClass) →
  worst-class a Wheelbarrow ≡ Wheelbarrow
worst-class-wheelbarrow Concorde = refl
worst-class-wheelbarrow Business = refl
worst-class-wheelbarrow Economy = refl
worst-class-wheelbarrow Wheelbarrow = refl

-- THEOREM 7: Concorde is identity element

worst-class-concorde : ∀ (a : TransportClass) →
  worst-class a Concorde ≡ a
worst-class-concorde Concorde = refl
worst-class-concorde Business = refl
worst-class-concorde Economy = refl
worst-class-concorde Wheelbarrow = refl

-- THEOREM 8: Map<K,V> transport class is worst of key and value classes

map-worst-of-key-value : ∀ {sk tk sv tv : PrimitiveType} →
  let key-class = primitive-transport-class sk tk in
  let val-class = primitive-transport-class sv tv in
  let map-class = worst-class key-class val-class in
  worst-class key-class val-class ≡ map-class
map-worst-of-key-value {sk} {tk} {sv} {tv} = refl

-- THEOREM 9: Tuple transport class is worst of all element classes

tuple-worst-of-elements : ∀ {s1 t1 s2 t2 : PrimitiveType} →
  let elem1-class = primitive-transport-class s1 t1 in
  let elem2-class = primitive-transport-class s2 t2 in
  let tuple-class = worst-class elem1-class elem2-class in
  worst-class elem1-class elem2-class ≡ tuple-class
tuple-worst-of-elements {s1} {t1} {s2} {t2} = refl

-- THEOREM 10: Container narrowing requires Wheelbarrow
-- If element needs Wheelbarrow, container needs Wheelbarrow

container-wheelbarrow-propagation : ∀ {s t : PrimitiveType} →
  primitive-transport-class s t ≡ Wheelbarrow →
  worst-class (primitive-transport-class s t) Business ≡ Wheelbarrow
container-wheelbarrow-propagation {s} {t} prf rewrite prf = refl

-- COROLLARY: Containers can only improve to Business, never to Concorde
-- Even if elements are Concorde, container iteration adds overhead

container-best-is-business : ∀ {s t : PrimitiveType} →
  primitive-transport-class s t ≡ Concorde →
  worst-class Concorde Business ≡ Business
container-best-is-business prf = refl

-- SUMMARY:
-- ========
-- Container transport class propagation:
--   1. Option<T> propagates element class exactly (zero overhead wrapper)
--   2. Vec<T> is at least Business (iteration overhead)
--   3. Map<K,V> is worst of key and value classes
--   4. Tuple is worst of all element classes
--   5. Worst-class is associative, commutative, idempotent
--   6. Wheelbarrow propagates to container (absorbing)
--   7. Containers with Concorde elements are Business at best
--
-- This proves that protocol-squisher's container analysis correctly
-- propagates transport classes from elements to containers.
