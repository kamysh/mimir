{-# OPTIONS --safe #-}
-- Magnitudes of all representable signed integers fit their unsigned width.
module Mimir.SignedIntegerBounds where

open import Data.Nat using (ℕ; suc; _≤_; s≤s; _+_)
import Data.Nat.Properties as NP
open import Data.Integer using (+_; -[1+_])
import Data.Integer as Int
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (subst)
open import Mimir.Binary64 using (power; powerMinusOne)
import Mimir.SignedMachine as Machine
import Mimir.SignedMagnitude as Magnitude

fitsUnsigned : ∀ bits → power bits ≤ powerMinusOne (suc bits)
fitsUnsigned bits = s≤s (NP.m≤m+n (powerMinusOne bits) (powerMinusOne bits + 0))

module Width (bits : ℕ) where
  private
    module W = Machine.Width bits

  positive : ∀ number → W.InRange (+ number) → number ≤ powerMinusOne bits
  positive number (above , below) = Int.drop‿+≤+
    (subst (+ number Int.≤_) (Magnitude.Width.maximum bits) below)

  negative : ∀ number → W.InRange -[1+ number ] → suc number ≤ power bits
  negative number range = s≤s (Int.drop‿-≤- (Data.Product.proj₁ range))

  positiveUnsigned : ∀ number → W.InRange (+ number) → number ≤ powerMinusOne (suc bits)
  positiveUnsigned number range = NP.≤-trans (positive number range)
    (NP.≤-trans (NP.n≤1+n (powerMinusOne bits)) (fitsUnsigned bits))

  negativeUnsigned : ∀ number → W.InRange -[1+ number ] → suc number ≤ powerMinusOne (suc bits)
  negativeUnsigned number range = NP.≤-trans (negative number range) (fitsUnsigned bits)
