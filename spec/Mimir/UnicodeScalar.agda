{-# OPTIONS --safe #-}
-- Construct canonical UTF-8 from every Unicode scalar number, including
-- unassigned and noncharacter scalar values. Surrogates are excluded.
module Mimir.UnicodeScalar where

open import Data.List using (List; _++_)
open import Data.Nat using (ℕ; suc; _+_; _≤_; _≤?_; _<_; _<?_; z≤n; s≤s)
open import Data.Nat.Properties using (m≤m+n; ≮⇒≥; ≤-<-trans; ≤-trans; ≤-irrelevant; <-irrefl)
open import Data.Product using (_×_; _,_; Σ; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable.Core using (_×-dec_; _⊎-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans)
open import Data.Empty using (⊥-elim)
open import Mimir.Bits using (Word; Byte)
import Mimir.Bits as Bits
import Mimir.UTF8Packet as Packet

Valid : ℕ → Set
Valid number = number ≤ 1114111 × (number < 55296 ⊎ 57344 ≤ number)

valid? : ∀ number → Dec (Valid number)
valid? number = (number ≤? 1114111) ×-dec ((number <? 55296) ⊎-dec (57344 ≤? number))

record Encoded (number : ℕ) : Set where
  constructor encoded
  field value : Packet.Scalar; exact : Packet.codePoint (Packet.Scalar.raw value) ≡ number

canonicalFromNumber : ∀ raw number minimum →
  Packet.codePoint raw ≡ number → Packet.minimum raw ≡ minimum →
  minimum ≤ number → Valid number → Packet.Canonical raw
canonicalFromNumber raw number minimum same minimumSame low valid rewrite same | minimumSame = low , valid

build : ∀ width minimum (assemble : Word width → Packet.Raw) →
  (∀ word → Packet.codePoint (assemble word) ≡ Bits.Binary.value word) →
  (∀ word → Packet.minimum (assemble word) ≡ minimum) →
  ∀ number → minimum ≤ number → number < Bits.Binary.power width → Valid number → Encoded number
build width minimum assemble codeLaw minimumLaw number low bound valid =
  encoded (Packet.scalar raw (canonicalFromNumber raw number minimum exact (minimumLaw word) low valid)) exact
  where
  word = Bits.Binary.Expansion.digits (Bits.Binary.encode width number bound)
  raw = assemble word
  exact = trans (codeLaw word) (Bits.Binary.decodeEncode width number bound)

-- Keep the symbolic arithmetic proof opaque before applying Unicode-sized
-- constants; no million-constructor inequality is unfolded at the call site.
abstract
  belowPadding : ∀ number padding → number < suc (number + padding)
  belowPadding number padding = s≤s (m≤m+n number padding)

  padding : ∀ number extra → number ≤ number + extra
  padding = m≤m+n

outsideIrrelevant : ∀ number (first second : number < 55296 ⊎ 57344 ≤ number) → first ≡ second
outsideIrrelevant number (inj₁ first) (inj₁ second) = cong inj₁ (≤-irrelevant first second)
outsideIrrelevant number (inj₂ first) (inj₂ second) = cong inj₂ (≤-irrelevant first second)
outsideIrrelevant number (inj₁ before) (inj₂ after) =
  ⊥-elim (<-irrefl refl (≤-<-trans (≤-trans (padding 55296 2048) after) before))
outsideIrrelevant number (inj₂ after) (inj₁ before) =
  ⊥-elim (<-irrefl refl (≤-<-trans (≤-trans (padding 55296 2048) after) before))

validIrrelevant : ∀ number (first second : Valid number) → first ≡ second
validIrrelevant number (firstBound , firstOutside) (secondBound , secondOutside) =
  cong₂ _,_ (≤-irrelevant firstBound secondBound) (outsideIrrelevant number firstOutside secondOutside)

encode : ∀ number → Valid number → Encoded number
encode number valid with number <? 128
... | yes small = build 7 0 Packet.fromSeven Packet.fromSevenValue Packet.fromSevenMinimum number z≤n small valid
... | no notSmall with number <? 2048
...   | yes medium = build 11 128 Packet.fromEleven Packet.fromElevenValue Packet.fromElevenMinimum number (≮⇒≥ notSmall) medium valid
...   | no notMedium with number <? 65536
...     | yes large = build 16 2048 Packet.fromSixteen Packet.fromSixteenValue Packet.fromSixteenMinimum number (≮⇒≥ notMedium) large valid
...     | no notLarge = build 21 65536 Packet.fromTwentyOne Packet.fromTwentyOneValue Packet.fromTwentyOneMinimum number
      (≮⇒≥ notLarge) (≤-<-trans (proj₁ valid) (belowPadding 1114111 983040)) valid

decodeEncodedNumber : ∀ number valid suffix →
  Σ (Packet.Decoded (Packet.encode (Packet.Scalar.raw (Encoded.value (encode number valid))) ++ suffix))
    (λ result → Packet.decode (Packet.encode (Packet.Scalar.raw (Encoded.value (encode number valid))) ++ suffix) ≡ inj₂ result ×
      (Packet.codePoint (Packet.Scalar.raw (Packet.Decoded.value result)) ≡ number × Packet.Decoded.suffix result ≡ suffix))
decodeEncodedNumber number valid suffix with encode number valid
... | encoded (Packet.scalar raw canonical) exact with Packet.decodeComplete raw canonical suffix
...   | result , observed , sameRaw , sameSuffix = result , observed ,
      trans (cong Packet.codePoint sameRaw) exact , sameSuffix
