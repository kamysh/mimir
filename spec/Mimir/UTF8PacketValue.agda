{-# OPTIONS --safe #-}
-- Numeric packet assembly through the existing checked bit conversions.
-- General identities are checked before concrete Unicode bounds are applied.
module Mimir.UTF8PacketValue where

open import Data.Vec using ([]; _∷_; _++_)
open import Data.Nat using (_+_; _*_; _<_)
open import Data.Nat.Properties using (*-comm)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import Mimir.Bits using (Word)
import Mimir.Bits as Bits
import Mimir.UTF8Packet as P

twoAssembly : ∀ (low : Word 6) high → P.fromEleven (low ++ high) ≡ P.two high low
twoAssembly (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ []) high = refl

threeAssembly : ∀ (low middle : Word 6) high →
  P.fromSixteen (low ++ (middle ++ high)) ≡ P.three high middle low
threeAssembly (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ []) (g ∷ h ∷ i ∷ j ∷ k ∷ l ∷ []) high = refl

fourAssembly : ∀ (low next middle : Word 6) high →
  P.fromTwentyOne (low ++ (next ++ (middle ++ high))) ≡ P.four high middle next low
fourAssembly (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ []) (g ∷ h ∷ i ∷ j ∷ k ∷ l ∷ [])
  (m ∷ n ∷ o ∷ p ∷ q ∷ r ∷ []) high = refl

abstract
  appendSix : ∀ {width} (low : Word 6) (high : Word width) →
    Bits.Binary.value (low ++ high) ≡ Bits.Binary.value low + 64 * Bits.Binary.value high
  appendSix low high = trans (Bits.Binary.valueAppend low high)
    (cong (Bits.Binary.value low +_) (*-comm (Bits.Binary.value high) 64))

  twoWhole : ∀ high low → P.codePoint (P.two high low) ≡ Bits.Binary.value (low ++ high)
  twoWhole high low = trans (cong P.codePoint (sym (twoAssembly low high))) (P.fromElevenValue (low ++ high))

  threeWhole : ∀ high middle low → P.codePoint (P.three high middle low) ≡ Bits.Binary.value (low ++ (middle ++ high))
  threeWhole high middle low = trans (cong P.codePoint (sym (threeAssembly low middle high)))
    (P.fromSixteenValue (low ++ (middle ++ high)))

  fourWhole : ∀ high middle next low → P.codePoint (P.four high middle next low) ≡
    Bits.Binary.value (low ++ (next ++ (middle ++ high)))
  fourWhole high middle next low = trans (cong P.codePoint (sym (fourAssembly low next middle high)))
    (P.fromTwentyOneValue (low ++ (next ++ (middle ++ high))))

  twoLinear : ∀ high low → P.codePoint (P.two high low) ≡ Bits.Binary.value low + 64 * Bits.Binary.value high
  twoLinear high low = trans (twoWhole high low) (appendSix low high)

  threeLinear : ∀ high middle low → P.codePoint (P.three high middle low) ≡
    Bits.Binary.value low + 64 * (Bits.Binary.value middle + 64 * Bits.Binary.value high)
  threeLinear high middle low = trans (threeWhole high middle low)
    (trans (appendSix low (middle ++ high))
      (cong (λ value → Bits.Binary.value low + 64 * value) (appendSix middle high)))

  fourLinear : ∀ high middle next low → P.codePoint (P.four high middle next low) ≡
    Bits.Binary.value low + 64 * (Bits.Binary.value next + 64 * (Bits.Binary.value middle + 64 * Bits.Binary.value high))
  fourLinear high middle next low = trans (fourWhole high middle next low)
    (trans (appendSix low (next ++ (middle ++ high)))
      (cong (λ value → Bits.Binary.value low + 64 * value)
        (trans (appendSix next (middle ++ high))
          (cong (λ value → Bits.Binary.value next + 64 * value) (appendSix middle high)))))

  twoBound : ∀ high low → P.codePoint (P.two high low) < Bits.Binary.power 11
  twoBound high low = subst (_< Bits.Binary.power 11) (sym (twoWhole high low)) (Bits.Binary.valueBound (low ++ high))

  threeBound : ∀ high middle low → P.codePoint (P.three high middle low) < Bits.Binary.power 16
  threeBound high middle low = subst (_< Bits.Binary.power 16) (sym (threeWhole high middle low))
    (Bits.Binary.valueBound (low ++ (middle ++ high)))

  fourBound : ∀ high middle next low → P.codePoint (P.four high middle next low) < Bits.Binary.power 21
  fourBound high middle next low = subst (_< Bits.Binary.power 21) (sym (fourWhole high middle next low))
    (Bits.Binary.valueBound (low ++ (next ++ (middle ++ high))))
