{-# OPTIONS --safe #-}
module Mimir.VectorFill where

open import Data.Nat using (ℕ; _∸_; _≤_)
open import Data.Nat.Properties using (m+[n∸m]≡n)
open import Data.List as List using (List)
open import Data.Vec using (Vec; _++_; replicate; toList)
open import Data.Vec.Properties using (toList-++; toList-replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; trans)

castList : ∀ {A : Set} {first second} (same : first ≡ second) (input : Vec A first) → toList (subst (Vec A) same input) ≡ toList input
castList refl input = refl

fill : ∀ {A : Set} {size} target → Vec A size → size ≤ target → A → Vec A target
fill {size = size} target input bounded filler = subst (Vec _) (m+[n∸m]≡n bounded) (input ++ replicate (target ∸ size) filler)

exact : ∀ {A : Set} {size} target (input : Vec A size) bounded filler →
  toList (fill target input bounded filler) ≡ toList input List.++ List.replicate (target ∸ size) filler
exact {size = size} target input bounded filler =
  trans (castList (m+[n∸m]≡n bounded) (input ++ replicate (target ∸ size) filler))
  (trans (toList-++ input (replicate (target ∸ size) filler))
    (cong (toList input List.++_) (toList-replicate (target ∸ size) filler)))
