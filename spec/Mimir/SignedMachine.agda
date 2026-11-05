{-# OPTIONS --safe #-}
-- Fixed-width signed arithmetic. Wrapping and saturating operations are
-- distinct; serde_json uses both for different exponent operations.
module Mimir.SignedMachine where

import Data.Empty
open import Data.Product using (_×_; _,_)
open import Data.Nat using (ℕ; suc; z≤n; s≤s⁻¹)
open import Data.Integer using (ℤ; +_; -[1+_]; _+_; _-_; -_; _≤_; _≤?_; +≤+)
open import Data.Integer.Properties using (≤-refl; ≤-trans; +-monoˡ-≤; +-identityˡ;
  +-assoc; +-inverseʳ; +-inverseˡ; +-identityʳ)
open import Data.Integer.DivMod using (_%ℕ_; n%ℕd<d)
open import Data.Nat.DivMod using (m≤n⇒m%n≡m)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; subst)
open import Mimir.Binary64 using (power; powerMinusOne)

cancelPlus : ∀ number offset → (number + offset) - offset ≡ number
cancelPlus number offset = trans (+-assoc number offset (- offset))
  (trans (cong (λ other → number + other) (+-inverseʳ offset)) (+-identityʳ number))

cancelMinus : ∀ number offset → (number - offset) + offset ≡ number
cancelMinus number offset = trans (+-assoc number (- offset) offset)
  (trans (cong (λ other → number + other) (+-inverseˡ offset)) (+-identityʳ number))

smallRemainder : ∀ number maximum → + 0 ≤ number → number ≤ + maximum →
  + (number %ℕ suc maximum) ≡ number
smallRemainder (+ number) maximum nonnegative (+≤+ bounded) = cong +_ (m≤n⇒m%n≡m bounded)
smallRemainder (-[1+ number ]) maximum () bounded

data OverflowChecks : Set where enabled disabled : OverflowChecks

module Width (magnitudeBits : ℕ) where
  offset : ℤ
  offset = + power magnitudeBits

  minimum maximum : ℤ
  minimum = - offset
  maximum = + powerMinusOne (suc magnitudeBits) - offset

  ordered : minimum ≤ maximum
  ordered = subst (_≤ maximum) (+-identityˡ minimum)
    (+-monoˡ-≤ minimum (+≤+ (z≤n {n = powerMinusOne (suc magnitudeBits)})))

  record Integer : Set where
    constructor integer
    field number : ℤ; above : minimum ≤ number; below : number ≤ maximum

  InRange : ℤ → Set
  InRange number = minimum ≤ number × number ≤ maximum

  wrapValue : ℤ → ℤ
  wrapValue number = + ((number + offset) %ℕ power (suc magnitudeBits)) - offset

  wrap : ℤ → Integer
  wrap number = integer (wrapValue number)
    (subst (_≤ wrapValue number) (+-identityˡ minimum)
      (+-monoˡ-≤ minimum (+≤+ (z≤n {n = (number + offset) %ℕ power (suc magnitudeBits)}))))
    (+-monoˡ-≤ minimum (+≤+ (s≤s⁻¹ (n%ℕd<d (number + offset) (power (suc magnitudeBits))))))

  wrapExact : ∀ number → minimum ≤ number → number ≤ maximum → wrapValue number ≡ number
  wrapExact number above below = trans (cong (_- offset) (smallRemainder (number + offset)
    (powerMinusOne (suc magnitudeBits))
    (subst (_≤ number + offset) (+-inverseˡ offset) (+-monoˡ-≤ offset above))
    (subst (number + offset ≤_) (cancelMinus (+ powerMinusOne (suc magnitudeBits)) offset) (+-monoˡ-≤ offset below))))
    (cancelPlus number offset)

  wrapIdempotent : ∀ number → wrapValue (wrapValue number) ≡ wrapValue number
  wrapIdempotent number = wrapExact (wrapValue number) (Integer.above (wrap number)) (Integer.below (wrap number))

  saturate : ℤ → Integer
  saturate number with minimum ≤? number
  ... | no under = integer minimum ≤-refl ordered
  ... | yes above with number ≤? maximum
  ...   | no over = integer maximum ordered ≤-refl
  ...   | yes below = integer number above below

  saturateExact : ∀ number → minimum ≤ number → number ≤ maximum → Integer.number (saturate number) ≡ number
  saturateExact number above below with minimum ≤? number
  ... | no impossible = Data.Empty.⊥-elim (impossible above)
  ... | yes accepted with number ≤? maximum
  ...   | no impossible = Data.Empty.⊥-elim (impossible below)
  ...   | yes acceptedUpper = refl

  wrappingAdd : Integer → Integer → Integer
  wrappingAdd first second = wrap (Integer.number first + Integer.number second)

  wrappingSubtract : Integer → Integer → Integer
  wrappingSubtract first second = wrap (Integer.number first - Integer.number second)

  saturatingAdd : Integer → ℤ → Integer
  saturatingAdd first second = saturate (Integer.number first + second)

  saturatingSubtract : Integer → ℤ → Integer
  saturatingSubtract first second = saturate (Integer.number first - second)

  data Evaluation (input : ℤ) : Set where
    returned : Integer → Evaluation input
    panic : ¬ InRange input → Evaluation input

  execute : OverflowChecks → ∀ input → Evaluation input
  execute disabled input = returned (wrap input)
  execute enabled input with minimum ≤? input
  ... | no below = panic (λ { (above , _) → below above })
  ... | yes above with input ≤? maximum
  ...   | no over = panic (λ { (_ , below) → over below })
  ...   | yes below = returned (integer input above below)

  checkedReturnExact : ∀ input result → execute enabled input ≡ returned result → Integer.number result ≡ input
  checkedReturnExact input result observed with minimum ≤? input
  ... | no below with observed
  ...   | ()
  checkedReturnExact input result observed | yes above with input ≤? maximum
  ... | no over with observed
  ...   | ()
  checkedReturnExact input result observed | yes above | yes below with observed
  ... | refl = refl
