{-# OPTIONS --safe #-}
-- The finite predicate used for the complete Unicode conversion proof.
module Mimir.ScalarCharacterCheck where

import Data.Char as Char
open import Data.Bool using (Bool; true; T)
open import Data.Nat using (ℕ; _≟_)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (does; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Mimir.UnicodeScalar as Scalar
import Mimir.FiniteBooleanRange as Range

test : ℕ → Bool
test number with Scalar.valid? number
... | no outside = true
... | yes valid = does (Char.toℕ (Char.fromℕ number) ≟ number)

testSound : ∀ number → Scalar.Valid number → T (test number) →
  Char.toℕ (Char.fromℕ number) ≡ number
testSound number valid checked with Scalar.valid? number
... | no outside = ⊥-elim (outside valid)
... | yes admitted = ≡ᵇ⇒≡ (Char.toℕ (Char.fromℕ number)) number checked

module C = Range.Check test
