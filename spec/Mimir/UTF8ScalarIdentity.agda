{-# OPTIONS --safe #-}
-- Canonical UTF-8 packets are uniquely determined by their scalar number.
-- This closes the identity connection between byte-key and text-key maps.
module Mimir.UTF8ScalarIdentity where

import Data.Vec as V
import Data.Vec.Properties as VP
open import Data.Nat using (ℕ; _<_; _≤_)
open import Data.Nat.Properties using (≤-trans; <-≤-trans; <-irrefl)
open import Data.Product using (proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
import Mimir.Bits as Bits
import Mimir.UTF8Packet as P
import Mimir.UnicodeScalar as U

abstract
  oneValue : ∀ payload → P.codePoint (P.one payload) ≡ Bits.Binary.value payload
  oneValue = P.fromSevenValue

  twoValue : ∀ high low → P.codePoint (P.two high low) ≡ Bits.Binary.value (low V.++ high)
  twoValue high (a V.∷ b V.∷ c V.∷ d V.∷ e V.∷ f V.∷ V.[]) =
    P.fromElevenValue (a V.∷ b V.∷ c V.∷ d V.∷ e V.∷ f V.∷ high)

  threeValue : ∀ high middle low → P.codePoint (P.three high middle low) ≡ Bits.Binary.value (low V.++ (middle V.++ high))
  threeValue high (g V.∷ h V.∷ i V.∷ j V.∷ k V.∷ l V.∷ V.[])
    (a V.∷ b V.∷ c V.∷ d V.∷ e V.∷ f V.∷ V.[]) =
    P.fromSixteenValue (a V.∷ b V.∷ c V.∷ d V.∷ e V.∷ f V.∷ g V.∷ h V.∷ i V.∷ j V.∷ k V.∷ l V.∷ high)

  fourValue : ∀ high middle next low → P.codePoint (P.four high middle next low) ≡
    Bits.Binary.value (low V.++ (next V.++ (middle V.++ high)))
  fourValue high (m V.∷ n V.∷ o V.∷ p V.∷ q V.∷ r V.∷ V.[])
    (g V.∷ h V.∷ i V.∷ j V.∷ k V.∷ l V.∷ V.[])
    (a V.∷ b V.∷ c V.∷ d V.∷ e V.∷ f V.∷ V.[]) =
    P.fromTwentyOneValue (a V.∷ b V.∷ c V.∷ d V.∷ e V.∷ f V.∷ g V.∷ h V.∷ i V.∷ j V.∷ k V.∷ l V.∷
      m V.∷ n V.∷ o V.∷ p V.∷ q V.∷ r V.∷ high)

  oneBound : ∀ payload → P.codePoint (P.one payload) < 128
  oneBound payload = subst (_< 128) (sym (oneValue payload)) (Bits.Binary.valueBound payload)

  twoBound : ∀ high low → P.codePoint (P.two high low) < 2048
  twoBound high low = subst (_< 2048) (sym (twoValue high low)) (Bits.Binary.valueBound (low V.++ high))

  threeBound : ∀ high middle low → P.codePoint (P.three high middle low) < 65536
  threeBound high middle low = subst (_< 65536) (sym (threeValue high middle low))
    (Bits.Binary.valueBound (low V.++ (middle V.++ high)))

apart : ∀ first second bound → first < bound → bound ≤ second → first ≢ second
apart first second bound below above refl = <-irrefl refl (<-≤-trans below above)

sameOne : ∀ first second → P.codePoint (P.one first) ≡ P.codePoint (P.one second) → P.one first ≡ P.one second
sameOne first second same = cong P.one (Bits.Binary.valueInjective first second
  (trans (sym (oneValue first)) (trans same (oneValue second))))

sameTwo : ∀ high low high′ low′ → P.codePoint (P.two high low) ≡ P.codePoint (P.two high′ low′) →
  P.two high low ≡ P.two high′ low′
sameTwo high low high′ low′ same = cong₂ P.two (proj₂ chunks) (proj₁ chunks)
  where
  chunks = VP.++-injective low low′ (Bits.Binary.valueInjective (low V.++ high) (low′ V.++ high′)
    (trans (sym (twoValue high low)) (trans same (twoValue high′ low′))))

sameThree : ∀ high middle low high′ middle′ low′ →
  P.codePoint (P.three high middle low) ≡ P.codePoint (P.three high′ middle′ low′) →
  P.three high middle low ≡ P.three high′ middle′ low′
sameThree high middle low high′ middle′ low′ same =
  cong₂ (λ assemble payload → assemble payload)
    (cong₂ P.three (proj₂ upper) (proj₁ upper)) (proj₁ lower)
  where
  lower = VP.++-injective low low′ (Bits.Binary.valueInjective (low V.++ (middle V.++ high)) (low′ V.++ (middle′ V.++ high′))
    (trans (sym (threeValue high middle low)) (trans same (threeValue high′ middle′ low′))))
  upper = VP.++-injective middle middle′ (proj₂ lower)

sameFour : ∀ high middle next low high′ middle′ next′ low′ →
  P.codePoint (P.four high middle next low) ≡ P.codePoint (P.four high′ middle′ next′ low′) →
  P.four high middle next low ≡ P.four high′ middle′ next′ low′
sameFour high middle next low high′ middle′ next′ low′ same =
  cong₂ (λ assemble payload → assemble payload)
    (cong₂ (λ assemble payload → assemble payload)
      (cong₂ P.four (proj₂ upper) (proj₁ upper)) (proj₁ center)) (proj₁ lower)
  where
  lower = VP.++-injective low low′ (Bits.Binary.valueInjective (low V.++ (next V.++ (middle V.++ high)))
    (low′ V.++ (next′ V.++ (middle′ V.++ high′)))
    (trans (sym (fourValue high middle next low)) (trans same (fourValue high′ middle′ next′ low′))))
  center = VP.++-injective next next′ (proj₂ lower)
  upper = VP.++-injective middle middle′ (proj₂ center)

rawUnique : ∀ first second → P.Canonical first → P.Canonical second →
  P.codePoint first ≡ P.codePoint second → first ≡ second
rawUnique (P.one first) (P.one second) validFirst validSecond = sameOne first second
rawUnique (P.two high low) (P.two high′ low′) validFirst validSecond = sameTwo high low high′ low′
rawUnique (P.three high middle low) (P.three high′ middle′ low′) validFirst validSecond = sameThree high middle low high′ middle′ low′
rawUnique (P.four high middle next low) (P.four high′ middle′ next′ low′) validFirst validSecond = sameFour high middle next low high′ middle′ next′ low′
rawUnique first@(P.one payload) second@(P.two _ _) validFirst validSecond same =
  ⊥-elim (apart _ _ 128 (oneBound payload) (proj₁ validSecond) same)
rawUnique first@(P.one payload) second@(P.three _ _ _) validFirst validSecond same =
  ⊥-elim (apart _ _ 128 (oneBound payload) (≤-trans (U.padding 128 1920) (proj₁ validSecond)) same)
rawUnique first@(P.one payload) second@(P.four _ _ _ _) validFirst validSecond same =
  ⊥-elim (apart _ _ 128 (oneBound payload) (≤-trans (U.padding 128 65408) (proj₁ validSecond)) same)
rawUnique first@(P.two _ _) second@(P.one payload) validFirst validSecond same =
  ⊥-elim (apart _ _ 128 (oneBound payload) (proj₁ validFirst) (sym same))
rawUnique first@(P.two high low) second@(P.three _ _ _) validFirst validSecond same =
  ⊥-elim (apart _ _ 2048 (twoBound high low) (proj₁ validSecond) same)
rawUnique first@(P.two high low) second@(P.four _ _ _ _) validFirst validSecond same =
  ⊥-elim (apart _ _ 2048 (twoBound high low) (≤-trans (U.padding 2048 63488) (proj₁ validSecond)) same)
rawUnique first@(P.three _ _ _) second@(P.one payload) validFirst validSecond same =
  ⊥-elim (apart _ _ 128 (oneBound payload) (≤-trans (U.padding 128 1920) (proj₁ validFirst)) (sym same))
rawUnique first@(P.three _ _ _) second@(P.two high low) validFirst validSecond same =
  ⊥-elim (apart _ _ 2048 (twoBound high low) (proj₁ validFirst) (sym same))
rawUnique first@(P.three high middle low) second@(P.four _ _ _ _) validFirst validSecond same =
  ⊥-elim (apart _ _ 65536 (threeBound high middle low) (proj₁ validSecond) same)
rawUnique first@(P.four _ _ _ _) second@(P.one payload) validFirst validSecond same =
  ⊥-elim (apart _ _ 128 (oneBound payload) (≤-trans (U.padding 128 65408) (proj₁ validFirst)) (sym same))
rawUnique first@(P.four _ _ _ _) second@(P.two high low) validFirst validSecond same =
  ⊥-elim (apart _ _ 2048 (twoBound high low) (≤-trans (U.padding 2048 63488) (proj₁ validFirst)) (sym same))
rawUnique first@(P.four _ _ _ _) second@(P.three high middle low) validFirst validSecond same =
  ⊥-elim (apart _ _ 65536 (threeBound high middle low) (proj₁ validFirst) (sym same))
