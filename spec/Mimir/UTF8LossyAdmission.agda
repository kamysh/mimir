{-# OPTIONS --safe #-}
-- Canonical payloads satisfy the exact leading/continuation checks of the
-- lossy reader, including E0, ED, F0 and F4 restricted second bytes.
module Mimir.UTF8LossyAdmission where

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ; _+_; _≤_; _≟_; z≤n; s≤s⁻¹)
open import Data.Nat.Properties using (m≤n+m; +-monoˡ-≤; 1+n≰n; ≤-trans)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Mimir.Bits using (Word)
import Mimir.Bits as Bits
import Mimir.UTF8Byte as B
import Mimir.UTF8Packet as P
import Mimir.UTF8CanonicalBounds as Bounds
import Mimir.UTF8CanonicalNecessity as Necessary
import Mimir.UTF8LossyConditions as Conditions
import Mimir.UTF8LossyGroup as G
import Mimir.UTF8LossyTail as T

abstract
  atZero : ∀ amount high middle → high ≡ 0 → (1 ≤ high ⊎ amount ≤ middle) → amount ≤ middle
  atZero amount .0 middle refl (inj₁ ())
  atZero amount .0 middle refl (inj₂ bounded) = bounded

  atThirteen : ∀ high middle → high ≡ 13 →
    (high ≤ 12 ⊎ ((high ≤ 13 × middle ≤ 31) ⊎ 14 ≤ high)) → middle ≤ 31
  atThirteen .13 middle refl (inj₁ impossible) = ⊥-elim (1+n≰n impossible)
  atThirteen .13 middle refl (inj₂ (inj₁ (upper , bounded))) = bounded
  atThirteen .13 middle refl (inj₂ (inj₂ impossible)) = ⊥-elim (1+n≰n impossible)

  atFour : ∀ high middle → high ≡ 4 → (high ≤ 3 ⊎ (high ≤ 4 × middle ≤ 15)) → middle ≤ 15
  atFour .4 middle refl (inj₁ impossible) = ⊥-elim (1+n≰n impossible)
  atFour .4 middle refl (inj₂ (upper , bounded)) = bounded

  highFourBound : ∀ high middle → (high ≤ 3 ⊎ (high ≤ 4 × middle ≤ 15)) → high ≤ 4
  highFourBound high middle (inj₁ below) = ≤-trans below (Bounds.padding 3 1)
  highFourBound high middle (inj₂ (below , restricted)) = below

single : ∀ word → T.Between 0 127 (B.singleByte word)
single word = subst (λ number → 0 ≤ number × number ≤ 127) (sym (B.singleNumeric word))
  (z≤n , s≤s⁻¹ (Bits.Binary.valueBound word))

continuationRange : ∀ (word : Word 6) lower upper → lower ≤ Bits.Binary.value word → Bits.Binary.value word ≤ upper →
  T.Between (lower + 128) (upper + 128) (B.continuationByte word)
continuationRange word lower upper above below = subst (λ number → lower + 128 ≤ number × number ≤ upper + 128)
  (sym (B.continuationNumeric word)) (+-monoˡ-≤ 128 above , +-monoˡ-≤ 128 below)

continuation : ∀ word → T.Between 128 191 (B.continuationByte word)
continuation word = continuationRange word 0 63 z≤n (s≤s⁻¹ (Bits.Binary.valueBound word))

two : ∀ high low → P.Canonical (P.two high low) → G.Leading G.two (B.twoByte high)
two high low canonical = subst (λ number → 194 ≤ number × number ≤ 223) (sym (B.twoNumeric high))
  (+-monoˡ-≤ 192 (Necessary.twoNecessary high low canonical) , +-monoˡ-≤ 192 (s≤s⁻¹ (Bits.Binary.valueBound high)))

three : ∀ high → G.Leading G.three (B.threeByte high)
three high = subst (λ number → 224 ≤ number × number ≤ 239) (sym (B.threeNumeric high))
  (m≤n+m 224 (Bits.Binary.value high) , +-monoˡ-≤ 224 (s≤s⁻¹ (Bits.Binary.valueBound high)))

four : ∀ high middle next low → P.Canonical (P.four high middle next low) → G.Leading G.four (B.fourByte high)
four high middle next low canonical = subst (λ number → 240 ≤ number × number ≤ 244) (sym (B.fourNumeric high))
  (m≤n+m 240 (Bits.Binary.value high) , +-monoˡ-≤ 240
    (highFourBound (Bits.Binary.value high) (Bits.Binary.value middle) (proj₂ (Necessary.fourNecessary high middle next low canonical))))

threeSecond : ∀ high middle low → P.Canonical (P.three high middle low) →
  Conditions.Second G.three (B.threeByte high) middle
threeSecond high middle low canonical with toℕ (B.threeByte high) ≟ 224
... | yes e0 = continuationRange middle 32 63
    (atZero 32 (Bits.Binary.value high) (Bits.Binary.value middle)
      (Conditions.shiftEqual (Bits.Binary.value high) 224 (toℕ (B.threeByte high)) 0 (B.threeNumeric high) e0)
      (proj₁ (Necessary.threeNecessary high middle low canonical))) (s≤s⁻¹ (Bits.Binary.valueBound middle))
... | no notE0 with toℕ (B.threeByte high) ≟ 237
...   | yes ed = continuationRange middle 0 31 z≤n
    (atThirteen (Bits.Binary.value high) (Bits.Binary.value middle)
      (Conditions.shiftEqual (Bits.Binary.value high) 224 (toℕ (B.threeByte high)) 13 (B.threeNumeric high) ed)
      (proj₂ (Necessary.threeNecessary high middle low canonical)))
...   | no notED = continuation middle

fourSecond : ∀ high middle next low → P.Canonical (P.four high middle next low) →
  Conditions.Second G.four (B.fourByte high) middle
fourSecond high middle next low canonical with toℕ (B.fourByte high) ≟ 240
... | yes f0 = continuationRange middle 16 63
    (atZero 16 (Bits.Binary.value high) (Bits.Binary.value middle)
      (Conditions.shiftEqual (Bits.Binary.value high) 240 (toℕ (B.fourByte high)) 0 (B.fourNumeric high) f0)
      (proj₁ (Necessary.fourNecessary high middle next low canonical))) (s≤s⁻¹ (Bits.Binary.valueBound middle))
... | no notF0 with toℕ (B.fourByte high) ≟ 244
...   | yes f4 = continuationRange middle 0 15 z≤n
    (atFour (Bits.Binary.value high) (Bits.Binary.value middle)
      (Conditions.shiftEqual (Bits.Binary.value high) 240 (toℕ (B.fourByte high)) 4 (B.fourNumeric high) f4)
      (proj₂ (Necessary.fourNecessary high middle next low canonical)))
...   | no notF4 = continuation middle
