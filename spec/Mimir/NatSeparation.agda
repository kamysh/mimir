{-# OPTIONS --safe #-}
-- Opaque general separation laws prevent repeated expansion of unary order
-- evidence when instantiated at large machine or Unicode boundaries.
module Mimir.NatSeparation where

open import Data.Nat using (ℕ; suc; _≤_; _<_)
open import Data.Nat.Properties using (≤-trans; 1+n≰n)
open import Data.Empty using (⊥)

abstract
  contradictory : ∀ {n upper} → suc upper ≤ n → n ≤ upper → ⊥
  contradictory lower upper = 1+n≰n (≤-trans lower upper)

  orderedCannotBeBefore : ∀ {lower value} → lower ≤ value → value < lower → ⊥
  orderedCannotBeBefore lower before = 1+n≰n (≤-trans before lower)
