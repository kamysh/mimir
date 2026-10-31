{-# OPTIONS --safe #-}
-- A numeric zero result from bitwise AND is equivalent to the independent
-- per-bit rule that every selected input bit is clear, for every word width.
module Mimir.BitMaskClear where

open import Data.Vec using ([]; _∷_; replicate)
open import Data.Vec.Properties using (∷-injectiveˡ; ∷-injectiveʳ)
open import Data.Nat using (ℕ; zero; suc; _≟_; _*_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Mimir.Bits using (Bit; Word; O; I)
import Mimir.Bits as Bits
import Mimir.BitLogic as Logic

zeros : ∀ width → Word width
zeros width = replicate width O

zerosValue : ∀ width → Bits.Binary.value (zeros width) ≡ 0
zerosValue zero = refl
zerosValue (suc width) = cong (_* 2) (zerosValue width)

zeroFromValue : ∀ {width} (word : Word width) → Bits.Binary.value word ≡ 0 → word ≡ zeros width
zeroFromValue {width} word observed = Bits.Binary.valueInjective word (zeros width) (trans observed (sym (zerosValue width)))

data Clear : ∀ {width} → Word width → Word width → Set where
  empty : Clear [] []
  ignored : ∀ {width bit} {word mask : Word width} → Clear word mask → Clear (bit ∷ word) (O ∷ mask)
  selected : ∀ {width} {word mask : Word width} → Clear word mask → Clear (O ∷ word) (I ∷ mask)

rightZero : ∀ bit → Logic.and bit O ≡ O
rightZero O = refl
rightZero I = refl

complete : ∀ {width} {word mask : Word width} → Clear word mask → Logic.wordAnd word mask ≡ zeros width
complete empty = refl
complete (ignored {bit = bit} rest) = cong₂ _∷_ (rightZero bit) (complete rest)
complete (selected rest) = cong (O ∷_) (complete rest)

sound : ∀ {width} (word mask : Word width) → Logic.wordAnd word mask ≡ zeros width → Clear word mask
sound [] [] observed = empty
sound (bit ∷ word) (O ∷ mask) observed = ignored (sound word mask (∷-injectiveʳ observed))
sound (O ∷ word) (I ∷ mask) observed = selected (sound word mask (∷-injectiveʳ observed))
sound (I ∷ word) (I ∷ mask) observed with ∷-injectiveˡ observed
... | ()

numericComplete : ∀ {width} {word mask : Word width} → Clear word mask → Bits.Binary.value (Logic.wordAnd word mask) ≡ 0
numericComplete {width} proof = trans (cong Bits.Binary.value (complete proof)) (zerosValue width)

numericSound : ∀ {width} (word mask : Word width) → Bits.Binary.value (Logic.wordAnd word mask) ≡ 0 → Clear word mask
numericSound word mask observed = sound word mask (zeroFromValue (Logic.wordAnd word mask) observed)

clear? : ∀ {width} (word mask : Word width) → Dec (Clear word mask)
clear? word mask with Bits.Binary.value (Logic.wordAnd word mask) ≟ 0
... | yes clear = yes (numericSound word mask clear)
... | no selectedBit = no (λ proof → selectedBit (numericComplete proof))
