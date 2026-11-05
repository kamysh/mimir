{-# OPTIONS --safe #-}
-- Negating a wrapped magnitude is exact throughout the signed negative range,
-- including the minimum value whose positive magnitude is not representable.
module Mimir.SignedMagnitude where

open import Data.Nat using (ℕ; suc; _+_; _*_; _≤_; s≤s⁻¹)
import Data.Nat.Properties as NP
import Data.Nat.DivMod as Mod
open import Data.Integer using (+_)
import Data.Integer as Int
import Data.Integer.Properties as IP
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)
open import Mimir.Binary64 using (power; powerMinusOne; powerStep)
import Mimir.SignedMachine as Machine

maximumSum : ∀ half → suc (2 * half) ≡ half + suc half
maximumSum half = trans (cong suc (cong (λ n → half + n) (NP.+-identityʳ half)))
  (sym (NP.+-suc half half))

maximumDifference : ∀ half → (+ suc (2 * half)) Int.- (+ suc half) ≡ + half
maximumDifference half = trans (cong (λ n → + n Int.- + suc half) (maximumSum half))
  (Machine.cancelPlus (+ half) (+ suc half))

twicePower : ∀ bits → power bits + power bits ≡ power (suc bits)
twicePower bits = trans
  (sym (cong (λ n → power bits + n) (NP.+-identityʳ (power bits))))
  (sym (powerStep bits))

module Width (bits : ℕ) where
  private
    module W = Machine.Width bits

  maximum : W.maximum ≡ + powerMinusOne bits
  maximum = maximumDifference (powerMinusOne bits)

  boundary : W.wrapValue W.offset ≡ W.minimum
  boundary = cong (λ remainder → + remainder Int.- W.offset)
    (trans (cong (λ n → n Mod.% power (suc bits)) (twicePower bits))
     (Mod.n%n≡0 (power (suc bits))))

  negateWrapped : ∀ magnitude → magnitude ≤ power bits →
    W.wrapValue (Int.- W.wrapValue (+ magnitude)) ≡ Int.- (+ magnitude)
  negateWrapped magnitude bounded with NP.m≤n⇒m<n∨m≡n bounded
  ... | inj₁ smaller = trans
    (cong (λ n → W.wrapValue (Int.- n))
     (W.wrapExact (+ magnitude) IP.neg-≤-pos
      (subst (+ magnitude Int.≤_) (sym maximum)
       (Int.+≤+ (s≤s⁻¹ smaller)))))
    (W.wrapExact (Int.- (+ magnitude))
     (IP.neg-mono-≤ (Int.+≤+ bounded))
     (subst (Int.- (+ magnitude) Int.≤_) (sym maximum) IP.neg-≤-pos))
  ... | inj₂ refl = trans (cong (λ n → W.wrapValue (Int.- n)) boundary) boundary
