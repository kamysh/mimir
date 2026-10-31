{-# OPTIONS --safe #-}
-- Canonicality conditions expressed in payload-word values. Bounds are
-- established symbolically before instantiating the Unicode constants.
module Mimir.UTF8CanonicalBounds where

open import Data.Nat using (ℕ; _+_; _*_; _≤_; _<_; suc; z≤n; s≤s; s≤s⁻¹)
open import Data.Nat.Properties using (≤-trans; m≤m+n; m≤n+m; +-mono-≤; *-monoʳ-≤)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (sym; subst)
import Mimir.Bits as Bits
import Mimir.UTF8Packet as P
import Mimir.UTF8PacketValue as Value

combine : ℕ → ℕ → ℕ
combine low high = low + 64 * high

abstract
  padding : ∀ lower extra → lower ≤ lower + extra
  padding = m≤m+n

  raiseLess : ∀ value upper extra → value < upper → value < upper + extra
  raiseLess value upper extra bounded = ≤-trans bounded (padding upper extra)

  scaledLower : ∀ scale low high lower → lower ≤ high → scale * lower ≤ low + scale * high
  scaledLower scale low high lower bounded = ≤-trans (*-monoʳ-≤ scale bounded) (m≤n+m (scale * high) low)

  combineLower : ∀ low high lower → lower ≤ low → lower ≤ combine low high
  combineLower low high lower bounded = ≤-trans bounded (padding low (64 * high))

  combineUpper : ∀ low high lowBound highBound → low ≤ lowBound → high ≤ highBound →
    combine low high ≤ combine lowBound highBound
  combineUpper low high lowBound highBound belowLow belowHigh = +-mono-≤ belowLow (*-monoʳ-≤ 64 belowHigh)

  oneCanonical : ∀ payload → P.Canonical (P.one payload)
  oneCanonical payload = z≤n ,
    (s≤s⁻¹ (raiseLess point 128 1113984 bounded) , inj₁ (raiseLess point 128 55168 bounded))
    where
    point : ℕ
    point = P.codePoint (P.one payload)
    bounded : point < 128
    bounded = subst (_< 128) (sym (P.fromSevenValue payload)) (Bits.Binary.valueBound payload)

  twoCanonical : ∀ high low → 2 ≤ Bits.Binary.value high → P.Canonical (P.two high low)
  twoCanonical high low minimum =
    subst (128 ≤_) (sym (Value.twoLinear high low))
      (scaledLower 64 (Bits.Binary.value low) (Bits.Binary.value high) 2 minimum) ,
    (s≤s⁻¹ (raiseLess (P.codePoint (P.two high low)) 2048 1112064 (Value.twoBound high low)) ,
      inj₁ (raiseLess (P.codePoint (P.two high low)) 2048 53248 (Value.twoBound high low)))

  threeMinimum : ∀ low middle high → 1 ≤ high ⊎ 32 ≤ middle → 2048 ≤ combine low (combine middle high)
  threeMinimum low middle high (inj₁ positive) = ≤-trans (padding 2048 2048)
    (scaledLower 64 low (combine middle high) 64 (scaledLower 64 middle high 1 positive))
  threeMinimum low middle high (inj₂ middleLarge) = scaledLower 64 low (combine middle high) 32
    (combineLower middle high 32 middleLarge)

  threeSurrogates : ∀ low middle high → low ≤ 63 → middle ≤ 63 →
    (high ≤ 12 ⊎ ((high ≤ 13 × middle ≤ 31) ⊎ 14 ≤ high)) →
    combine low (combine middle high) < 55296 ⊎ 57344 ≤ combine low (combine middle high)
  threeSurrogates low middle high lowBound middleBound (inj₁ highBound) = inj₁
    (raiseLess (combine low (combine middle high)) 53248 2048
      (s≤s (combineUpper low (combine middle high) 63 (combine 63 12) lowBound
        (combineUpper middle high 63 12 middleBound highBound))))
  threeSurrogates low middle high lowBound middleBound (inj₂ (inj₁ (highBound , restrictedMiddle))) = inj₁
    (s≤s (combineUpper low (combine middle high) 63 (combine 31 13) lowBound
      (combineUpper middle high 31 13 restrictedMiddle highBound)))
  threeSurrogates low middle high lowBound middleBound (inj₂ (inj₂ highBound)) = inj₂
    (scaledLower 64 low (combine middle high) 896 (scaledLower 64 middle high 14 highBound))

  threeCanonical : ∀ high middle low →
    (1 ≤ Bits.Binary.value high ⊎ 32 ≤ Bits.Binary.value middle) →
    (Bits.Binary.value high ≤ 12 ⊎ ((Bits.Binary.value high ≤ 13 × Bits.Binary.value middle ≤ 31) ⊎ 14 ≤ Bits.Binary.value high)) →
    P.Canonical (P.three high middle low)
  threeCanonical high middle low minimum surrogate =
    subst (2048 ≤_) (sym (Value.threeLinear high middle low))
      (threeMinimum (Bits.Binary.value low) (Bits.Binary.value middle) (Bits.Binary.value high) minimum) ,
    (s≤s⁻¹ (raiseLess (P.codePoint (P.three high middle low)) 65536 1048576 (Value.threeBound high middle low)) ,
      subst (λ number → number < 55296 ⊎ 57344 ≤ number) (sym (Value.threeLinear high middle low))
        (threeSurrogates (Bits.Binary.value low) (Bits.Binary.value middle) (Bits.Binary.value high)
          (s≤s⁻¹ (Bits.Binary.valueBound low)) (s≤s⁻¹ (Bits.Binary.valueBound middle)) surrogate))

  fourMinimum : ∀ low next middle high → 1 ≤ high ⊎ 16 ≤ middle →
    65536 ≤ combine low (combine next (combine middle high))
  fourMinimum low next middle high (inj₁ highBound) = ≤-trans (padding 65536 196608)
    (scaledLower 64 low (combine next (combine middle high)) 4096
      (scaledLower 64 next (combine middle high) 64 (scaledLower 64 middle high 1 highBound)))
  fourMinimum low next middle high (inj₂ middleBound) = scaledLower 64 low (combine next (combine middle high)) 1024
    (scaledLower 64 next (combine middle high) 16 (combineLower middle high 16 middleBound))

  fourMaximum : ∀ low next middle high → low ≤ 63 → next ≤ 63 → middle ≤ 63 →
    (high ≤ 3 ⊎ (high ≤ 4 × middle ≤ 15)) → combine low (combine next (combine middle high)) ≤ 1114111
  fourMaximum low next middle high lowBound nextBound middleBound (inj₁ highBound) =
    ≤-trans (combineUpper low (combine next (combine middle high)) 63 (combine 63 (combine 63 3)) lowBound
      (combineUpper next (combine middle high) 63 (combine 63 3) nextBound
        (combineUpper middle high 63 3 middleBound highBound))) (padding 1048575 65536)
  fourMaximum low next middle high lowBound nextBound middleBound (inj₂ (highBound , restrictedMiddle)) =
    combineUpper low (combine next (combine middle high)) 63 (combine 63 (combine 15 4)) lowBound
      (combineUpper next (combine middle high) 63 (combine 15 4) nextBound
        (combineUpper middle high 15 4 restrictedMiddle highBound))

  fourCanonical : ∀ high middle next low →
    (1 ≤ Bits.Binary.value high ⊎ 16 ≤ Bits.Binary.value middle) →
    (Bits.Binary.value high ≤ 3 ⊎ (Bits.Binary.value high ≤ 4 × Bits.Binary.value middle ≤ 15)) →
    P.Canonical (P.four high middle next low)
  fourCanonical high middle next low minimum maximum = lower ,
    (subst (_≤ 1114111) (sym (Value.fourLinear high middle next low))
      (fourMaximum (Bits.Binary.value low) (Bits.Binary.value next) (Bits.Binary.value middle) (Bits.Binary.value high)
        (s≤s⁻¹ (Bits.Binary.valueBound low)) (s≤s⁻¹ (Bits.Binary.valueBound next))
        (s≤s⁻¹ (Bits.Binary.valueBound middle)) maximum) , inj₂ (≤-trans (padding 57344 8192) lower))
    where
    lower : 65536 ≤ P.codePoint (P.four high middle next low)
    lower = subst (65536 ≤_) (sym (Value.fourLinear high middle next low))
      (fourMinimum (Bits.Binary.value low) (Bits.Binary.value next) (Bits.Binary.value middle) (Bits.Binary.value high) minimum)
