{-# OPTIONS --safe #-}
-- Select the first strictly greater boundary. Equality skips a boundary,
-- matching binary_search's found-index-plus-one convention on distinct keys.
module Mimir.UpperBoundary where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Nat using (ℕ; _≤_; _<_; _<?_; z≤n; s≤s)
open import Data.Nat.Properties using (≮⇒≥; <-irrefl; ≤-<-trans)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

module Search (Entry : Set) (key : Entry → ℕ) where
  data Boundary (needle : ℕ) : List Entry → List Entry → Entry → List Entry → Set where
    first : ∀ {entry rest} → needle < key entry → Boundary needle (entry ∷ rest) [] entry rest
    skip : ∀ {entry input before selected after} → key entry ≤ needle →
      Boundary needle input before selected after →
      Boundary needle (entry ∷ input) (entry ∷ before) selected after

  data Result (needle : ℕ) (input : List Entry) : Set where
    absent : All (λ entry → key entry ≤ needle) input → Result needle input
    selected : ∀ before entry after → Boundary needle input before entry after → Result needle input

  search : ∀ needle input → Result needle input
  search needle [] = absent []
  search needle (entry ∷ input) with needle <? key entry
  ... | yes greater = selected [] entry input (first greater)
  ... | no lower with search needle input
  ...   | absent allLower = absent (≮⇒≥ lower ∷ allLower)
  ...   | selected before chosen after proof = selected (entry ∷ before) chosen after (skip (≮⇒≥ lower) proof)

  exact : ∀ {needle input before entry after} → Boundary needle input before entry after →
    input ≡ before ++ entry ∷ after
  exact (first greater) = refl
  exact (skip {entry} lower proof) = cong (entry ∷_) (exact proof)

  priorLower : ∀ {needle input before entry after} → Boundary needle input before entry after →
    All (λ prior → key prior ≤ needle) before
  priorLower (first greater) = []
  priorLower (skip lower proof) = lower ∷ priorLower proof

  selectedGreater : ∀ {needle input before entry after} → Boundary needle input before entry after → needle < key entry
  selectedGreater (first greater) = greater
  selectedGreater (skip lower proof) = selectedGreater proof

  indexBound : ∀ {needle input before entry after} → Boundary needle input before entry after → length before < length input
  indexBound (first greater) = s≤s z≤n
  indexBound (skip lower proof) = s≤s (indexBound proof)

  contradiction : ∀ {needle input} → All (λ entry → key entry ≤ needle) input →
    Any (λ entry → needle < key entry) input → ⊥
  contradiction (lower ∷ rest) (here greater) = <-irrefl refl (≤-<-trans lower greater)
  contradiction (lower ∷ rest) (there later) = contradiction rest later

  unique : ∀ {needle input before entry after otherBefore otherEntry otherAfter} →
    Boundary needle input before entry after → Boundary needle input otherBefore otherEntry otherAfter →
    before ≡ otherBefore × entry ≡ otherEntry × after ≡ otherAfter
  unique (first greater) (first other) = refl , refl , refl
  unique (first greater) (skip lower proof) = ⊥-elim (<-irrefl refl (≤-<-trans lower greater))
  unique (skip lower proof) (first greater) = ⊥-elim (<-irrefl refl (≤-<-trans lower greater))
  unique (skip {entry} lower proof) (skip other rest) with unique proof rest
  ... | sameBefore , sameEntry , sameAfter = cong (entry ∷_) sameBefore , sameEntry , sameAfter

  record Covered (needle : ℕ) (input : List Entry) : Set where
    constructor covered
    field
      before : List Entry
      entry : Entry
      after : List Entry
      boundary : Boundary needle input before entry after

  selectCovered : ∀ needle input → Any (λ entry → needle < key entry) input → Covered needle input
  selectCovered needle input exists with search needle input
  ... | absent allLower = ⊥-elim (contradiction allLower exists)
  ... | selected before entry after proof = covered before entry after proof
