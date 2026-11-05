{-# OPTIONS --safe #-}
-- Nonempty Vec::pop behavior, keeping the complete prefix and removed item.
module Mimir.LastElement where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++)
open import Data.Nat using (ℕ; suc; _≤_; s≤s⁻¹)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; subst; sym)

module Over (A : Set) where
  record Popped (input : List A) : Set where
    constructor popped
    field prefix : List A; last : A; exact : input ≡ prefix ++ (last ∷ [])

  pop : ∀ first rest → Popped (first ∷ rest)
  pop first [] = popped [] first refl
  pop first (second ∷ rest) with pop second rest
  ... | popped prefix last exact = popped (first ∷ prefix) last (cong (first ∷_) exact)

  data View (input : List A) : Set where
    empty : input ≡ [] → View input
    nonempty : Popped input → View input

  view : ∀ input → View input
  view [] = empty refl
  view (first ∷ rest) = nonempty (pop first rest)

  lengthExact : ∀ {input} (result : Popped input) → length input ≡ suc (length (Popped.prefix result))
  lengthExact (popped prefix last exact) = trans (cong length exact)
    (trans (length-++ prefix) (trans (+-suc (length prefix) 0) (cong suc (+-identityʳ (length prefix)))))

  decreases : ∀ fuel {input} (result : Popped input) → length input ≤ suc fuel → length (Popped.prefix result) ≤ fuel
  decreases fuel result bounded = s≤s⁻¹ (subst (_≤ suc fuel) (lengthExact result) bounded)
