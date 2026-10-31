{-# OPTIONS --safe #-}
-- Reverse canonicality implications: a valid scalar cannot violate the
-- payload constraints used by the lossy reader and be replaced accidentally.
module Mimir.UTF8CanonicalNecessity where

open import Data.Nat using (ℕ; _≤_; _<_; _≤?_; suc; s≤s⁻¹)
open import Data.Nat.Properties using (≤-trans; 1+n≰n; ≰⇒>)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (subst)
import Mimir.Bits as Bits
import Mimir.UTF8Packet as P
import Mimir.UTF8PacketValue as Value
import Mimir.UTF8CanonicalBounds as Bounds
open Bounds using (combine)
open import Mimir.NatSeparation using (contradictory)

Range : ℕ → ℕ → Set
Range minimum value = minimum ≤ value × (value ≤ 1114111 × (value < 55296 ⊎ 57344 ≤ value))

abstract
  twoHigh : ∀ low high → low ≤ 63 → 128 ≤ combine low high → 2 ≤ high
  twoHigh low high lowBound minimum with high ≤? 1
  ... | no above = ≰⇒> above
  ... | yes tooSmall = ⊥-elim (contradictory minimum (Bounds.combineUpper low high 63 1 lowBound tooSmall))

  threeMinimum : ∀ low middle high → low ≤ 63 → 2048 ≤ combine low (combine middle high) →
    1 ≤ high ⊎ 32 ≤ middle
  threeMinimum low middle high lowBound minimum with high ≤? 0
  ... | no positive = inj₁ (≰⇒> positive)
  ... | yes zeroHigh with middle ≤? 31
  ...   | no largeMiddle = inj₂ (≰⇒> largeMiddle)
  ...   | yes tooSmall = ⊥-elim (contradictory {n = combine low (combine middle high)} {upper = 2047} minimum
      (Bounds.combineUpper low (combine middle high) 63 (combine 31 0) lowBound
        (Bounds.combineUpper middle high 31 0 tooSmall zeroHigh)))

  surrogateIntervalImpossible : ∀ value → 55296 ≤ value → value ≤ 57343 →
    value < 55296 ⊎ 57344 ≤ value → ⊥
  surrogateIntervalImpossible value lower upper (inj₁ before) = 1+n≰n (≤-trans before lower)
  surrogateIntervalImpossible value lower upper (inj₂ after) = contradictory after upper

  threeSurrogates : ∀ low middle high → low ≤ 63 → middle ≤ 63 →
    (combine low (combine middle high) < 55296 ⊎ 57344 ≤ combine low (combine middle high)) →
    high ≤ 12 ⊎ ((high ≤ 13 × middle ≤ 31) ⊎ 14 ≤ high)
  threeSurrogates low middle high lowBound middleBound surrogate with high ≤? 12
  ... | yes below = inj₁ below
  ... | no above12 with high ≤? 13
  ...   | no above13 = inj₂ (inj₂ (≰⇒> above13))
  ...   | yes atMost13 with middle ≤? 31
  ...     | yes restricted = inj₂ (inj₁ (atMost13 , restricted))
  ...     | no above31 = ⊥-elim (surrogateIntervalImpossible (combine low (combine middle high))
      (Bounds.scaledLower 64 low (combine middle high) 864
        (Bounds.combineUpper 32 13 middle high (≰⇒> above31) (≰⇒> above12)))
      (Bounds.combineUpper low (combine middle high) 63 (combine 63 13) lowBound
        (Bounds.combineUpper middle high 63 13 middleBound atMost13)) surrogate)

  fourMinimum : ∀ low next middle high → low ≤ 63 → next ≤ 63 →
    65536 ≤ combine low (combine next (combine middle high)) → 1 ≤ high ⊎ 16 ≤ middle
  fourMinimum low next middle high lowBound nextBound minimum = decide (high ≤? 0) (middle ≤? 15)
    where
    decide : Dec (high ≤ 0) → Dec (middle ≤ 15) → 1 ≤ high ⊎ 16 ≤ middle
    decide (no positive) middleDecision = inj₁ (≰⇒> positive)
    decide (yes zeroHigh) (no largeMiddle) = inj₂ (≰⇒> largeMiddle)
    decide (yes zeroHigh) (yes tooSmall) = ⊥-elim
      (contradictory {n = combine low (combine next (combine middle high))} {upper = 65535} minimum
        (Bounds.combineUpper low (combine next (combine middle high)) 63 (combine 63 (combine 15 0)) lowBound
          (Bounds.combineUpper next (combine middle high) 63 (combine 15 0) nextBound
            (Bounds.combineUpper middle high 15 0 tooSmall zeroHigh))))

  fourMaximum : ∀ low next middle high → combine low (combine next (combine middle high)) ≤ 1114111 →
    high ≤ 3 ⊎ (high ≤ 4 × middle ≤ 15)
  fourMaximum low next middle high maximum = decide (high ≤? 3) (high ≤? 4) (middle ≤? 15)
    where
    decide : Dec (high ≤ 3) → Dec (high ≤ 4) → Dec (middle ≤ 15) → high ≤ 3 ⊎ (high ≤ 4 × middle ≤ 15)
    decide (yes below) highDecision middleDecision = inj₁ below
    decide (no above3) (no above4) middleDecision = ⊥-elim (contradictory
        (≤-trans (Bounds.padding 1114112 196608)
          (Bounds.scaledLower 64 low (combine next (combine middle high)) 20480
            (Bounds.scaledLower 64 next (combine middle high) 320 (Bounds.scaledLower 64 middle high 5 (≰⇒> above4))))) maximum)
    decide (no above3) (yes atMost4) (yes restricted) = inj₂ (atMost4 , restricted)
    decide (no above3) (yes atMost4) (no above15) = ⊥-elim (contradictory
        (Bounds.scaledLower 64 low (combine next (combine middle high)) 17408
          (Bounds.scaledLower 64 next (combine middle high) 272
            (Bounds.combineUpper 16 4 middle high (≰⇒> above15) (≰⇒> above3)))) maximum)

  twoNecessary : ∀ high low → P.Canonical (P.two high low) → 2 ≤ Bits.Binary.value high
  twoNecessary high low canonical = twoHigh (Bits.Binary.value low) (Bits.Binary.value high)
    (s≤s⁻¹ (Bits.Binary.valueBound low)) (subst (128 ≤_) (Value.twoLinear high low) (proj₁ canonical))

  threeNecessary : ∀ high middle low → P.Canonical (P.three high middle low) →
    (1 ≤ Bits.Binary.value high ⊎ 32 ≤ Bits.Binary.value middle) ×
    (Bits.Binary.value high ≤ 12 ⊎ ((Bits.Binary.value high ≤ 13 × Bits.Binary.value middle ≤ 31) ⊎ 14 ≤ Bits.Binary.value high))
  threeNecessary high middle low canonical =
    threeMinimum (Bits.Binary.value low) (Bits.Binary.value middle) (Bits.Binary.value high)
      (s≤s⁻¹ (Bits.Binary.valueBound low)) (proj₁ numeric) ,
    threeSurrogates (Bits.Binary.value low) (Bits.Binary.value middle) (Bits.Binary.value high)
      (s≤s⁻¹ (Bits.Binary.valueBound low)) (s≤s⁻¹ (Bits.Binary.valueBound middle)) (proj₂ (proj₂ numeric))
    where
    numeric : Range 2048 (combine (Bits.Binary.value low) (combine (Bits.Binary.value middle) (Bits.Binary.value high)))
    numeric = subst (Range 2048) (Value.threeLinear high middle low) canonical

  fourNecessary : ∀ high middle next low → P.Canonical (P.four high middle next low) →
    (1 ≤ Bits.Binary.value high ⊎ 16 ≤ Bits.Binary.value middle) ×
    (Bits.Binary.value high ≤ 3 ⊎ (Bits.Binary.value high ≤ 4 × Bits.Binary.value middle ≤ 15))
  fourNecessary high middle next low canonical =
    fourMinimum (Bits.Binary.value low) (Bits.Binary.value next) (Bits.Binary.value middle) (Bits.Binary.value high)
      (s≤s⁻¹ (Bits.Binary.valueBound low)) (s≤s⁻¹ (Bits.Binary.valueBound next)) (proj₁ numeric) ,
    fourMaximum (Bits.Binary.value low) (Bits.Binary.value next) (Bits.Binary.value middle) (Bits.Binary.value high) (proj₁ (proj₂ numeric))
    where
    numeric : Range 65536 (combine (Bits.Binary.value low) (combine (Bits.Binary.value next) (combine (Bits.Binary.value middle) (Bits.Binary.value high))))
    numeric = subst (Range 65536) (Value.fourLinear high middle next low) canonical
