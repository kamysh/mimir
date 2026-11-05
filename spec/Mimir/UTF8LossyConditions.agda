{-# OPTIONS --safe #-}
-- Restricted UTF-8 lead/second-byte checks imply the word-level canonicality
-- conditions. No validity conclusion is taken from an unchecked Boolean.
module Mimir.UTF8LossyConditions where

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _≤?_; _≟_; z≤n; s≤s)
open import Data.Nat.Properties using (+-cancelʳ-≡; +-cancelʳ-≤; ≤-refl; ≤-reflexive; ≤-antisym; ≰⇒>)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Mimir.Bits using (Byte; Word)
import Mimir.Bits as Bits
import Mimir.UTF8Byte as B
import Mimir.UTF8LossyTail as T
import Mimir.UTF8LossyGroup as G
import Mimir.UTF8CanonicalBounds as Bounds

abstract
  shiftLower : ∀ value offset number lower → number ≡ value + offset → lower + offset ≤ number → lower ≤ value
  shiftLower value offset number lower exact bound = +-cancelʳ-≤ offset lower value
    (subst (lower + offset ≤_) exact bound)

  shiftUpper : ∀ value offset number upper → number ≡ value + offset → number ≤ upper + offset → value ≤ upper
  shiftUpper value offset number upper exact bound = +-cancelʳ-≤ offset value upper
    (subst (_≤ upper + offset) exact bound)

  shiftEqual : ∀ value offset number expected → number ≡ value + offset → number ≡ expected + offset → value ≡ expected
  shiftEqual value offset number expected exact equal = +-cancelʳ-≡ offset value expected (trans (sym exact) equal)

  shiftDifferent : ∀ value offset number expected → number ≡ value + offset → number ≢ expected + offset → value ≢ expected
  shiftDifferent value offset number expected exact different same = different (trans exact (cong (_+ offset) same))

  shiftPositive : ∀ value offset number → number ≡ value + offset → number ≢ offset → 1 ≤ value
  shiftPositive zero offset number exact different = ⊥-elim (different exact)
  shiftPositive (suc value) offset number exact different = s≤s z≤n

  avoidBoundary : ∀ boundary value → value ≢ suc boundary → value ≤ boundary ⊎ suc (suc boundary) ≤ value
  avoidBoundary boundary value different with value ≤? boundary
  ... | yes below = inj₁ below
  ... | no above with value ≤? suc boundary
  ...   | yes atMost = ⊥-elim (different (≤-antisym atMost (≰⇒> above)))
  ...   | no beyond = inj₂ (≰⇒> beyond)

  belowTop : ∀ boundary value → value ≤ suc boundary → value ≢ suc boundary → value ≤ boundary
  belowTop boundary value bounded different with value ≤? boundary
  ... | yes below = below
  ... | no above = ⊥-elim (different (≤-antisym bounded (≰⇒> above)))

secondBounds : ∀ width byte → 128 ≤ proj₁ (G.secondRange width byte) × proj₂ (G.secondRange width byte) ≤ 191
secondBounds G.two byte = ≤-refl , ≤-refl
secondBounds G.three byte with toℕ byte ≟ 224
... | yes e0 = Bounds.padding 128 32 , ≤-refl
... | no notE0 with toℕ byte ≟ 237
...   | yes ed = ≤-refl , Bounds.padding 159 32
...   | no notED = ≤-refl , ≤-refl
secondBounds G.four byte with toℕ byte ≟ 240
... | yes f0 = Bounds.padding 128 16 , ≤-refl
... | no notF0 with toℕ byte ≟ 244
...   | yes f4 = ≤-refl , Bounds.padding 143 48
...   | no notF4 = ≤-refl , ≤-refl

Second : G.Width → Byte → Word 6 → Set
Second width byte middle = T.Between (proj₁ (G.secondRange width byte)) (proj₂ (G.secondRange width byte))
  (B.continuationByte middle)

ThreeMinimum : Word 4 → Word 6 → Set
ThreeMinimum high middle = 1 ≤ Bits.Binary.value high ⊎ 32 ≤ Bits.Binary.value middle

ThreeSurrogates : Word 4 → Word 6 → Set
ThreeSurrogates high middle = Bits.Binary.value high ≤ 12 ⊎
  ((Bits.Binary.value high ≤ 13 × Bits.Binary.value middle ≤ 31) ⊎ 14 ≤ Bits.Binary.value high)

threeConditions : ∀ byte high middle → byte ≡ B.threeByte high → Second G.three byte middle →
  ThreeMinimum high middle × ThreeSurrogates high middle
threeConditions byte high middle encoded (lower , upper) with toℕ byte ≟ 224
... | yes e0 = inj₂ (shiftLower (Bits.Binary.value middle) 128 (toℕ (B.continuationByte middle)) 32
    (B.continuationNumeric middle) lower) ,
  inj₁ (subst (_≤ 12) (sym (shiftEqual (Bits.Binary.value high) 224 (toℕ byte) 0
    (trans (cong toℕ encoded) (B.threeNumeric high)) e0)) z≤n)
... | no notE0 with toℕ byte ≟ 237
...   | yes ed = inj₁ (shiftPositive (Bits.Binary.value high) 224 (toℕ byte)
    (trans (cong toℕ encoded) (B.threeNumeric high)) notE0) ,
  inj₂ (inj₁ (≤-reflexive (shiftEqual (Bits.Binary.value high) 224 (toℕ byte) 13
    (trans (cong toℕ encoded) (B.threeNumeric high)) ed) ,
    shiftUpper (Bits.Binary.value middle) 128 (toℕ (B.continuationByte middle)) 31 (B.continuationNumeric middle) upper))
...   | no notED with avoidBoundary 12 (Bits.Binary.value high)
    (shiftDifferent (Bits.Binary.value high) 224 (toℕ byte) 13 (trans (cong toℕ encoded) (B.threeNumeric high)) notED)
...     | inj₁ below = inj₁ (shiftPositive (Bits.Binary.value high) 224 (toℕ byte)
    (trans (cong toℕ encoded) (B.threeNumeric high)) notE0) , inj₁ below
...     | inj₂ above = inj₁ (shiftPositive (Bits.Binary.value high) 224 (toℕ byte)
    (trans (cong toℕ encoded) (B.threeNumeric high)) notE0) , inj₂ (inj₂ above)

FourMinimum : Word 3 → Word 6 → Set
FourMinimum high middle = 1 ≤ Bits.Binary.value high ⊎ 16 ≤ Bits.Binary.value middle

FourMaximum : Word 3 → Word 6 → Set
FourMaximum high middle = Bits.Binary.value high ≤ 3 ⊎ (Bits.Binary.value high ≤ 4 × Bits.Binary.value middle ≤ 15)

fourConditions : ∀ byte high middle → byte ≡ B.fourByte high → G.Leading G.four byte → Second G.four byte middle →
  FourMinimum high middle × FourMaximum high middle
fourConditions byte high middle encoded leading (lower , upper) with toℕ byte ≟ 240
... | yes f0 = inj₂ (shiftLower (Bits.Binary.value middle) 128 (toℕ (B.continuationByte middle)) 16
    (B.continuationNumeric middle) lower) ,
  inj₁ (subst (_≤ 3) (sym (shiftEqual (Bits.Binary.value high) 240 (toℕ byte) 0
    (trans (cong toℕ encoded) (B.fourNumeric high)) f0)) z≤n)
... | no notF0 with toℕ byte ≟ 244
...   | yes f4 = inj₁ (shiftPositive (Bits.Binary.value high) 240 (toℕ byte)
    (trans (cong toℕ encoded) (B.fourNumeric high)) notF0) ,
  inj₂ (≤-reflexive (shiftEqual (Bits.Binary.value high) 240 (toℕ byte) 4
    (trans (cong toℕ encoded) (B.fourNumeric high)) f4) ,
    shiftUpper (Bits.Binary.value middle) 128 (toℕ (B.continuationByte middle)) 15 (B.continuationNumeric middle) upper)
...   | no notF4 = inj₁ (shiftPositive (Bits.Binary.value high) 240 (toℕ byte)
    (trans (cong toℕ encoded) (B.fourNumeric high)) notF0) ,
  inj₁ (belowTop 3 (Bits.Binary.value high)
    (shiftUpper (Bits.Binary.value high) 240 (toℕ byte) 4 (trans (cong toℕ encoded) (B.fourNumeric high)) (proj₂ leading))
    (shiftDifferent (Bits.Binary.value high) 240 (toℕ byte) 4 (trans (cong toℕ encoded) (B.fourNumeric high)) notF4))
