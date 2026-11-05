{-# OPTIONS --safe #-}
-- Explicit fixed-width bit vectors bridge numeric wire bytes without Word8
-- foreign-function assumptions. Low bits come first, as in Radix.
module Mimir.Bits where

import Data.Fin as F
open import Data.Fin using (Fin; toℕ; fromℕ<)
open import Data.Fin.Properties using (toℕ<n; fromℕ<-toℕ; toℕ-fromℕ<; toℕ-injective)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
import Mimir.Radix as Radix

pattern O = F.zero
pattern I = F.suc F.zero

Bit = Fin 2
Word : ℕ → Set
Word = Vec Bit

module Binary = Radix.Base 1

abstract
  pack : ∀ {width} → Word width → Fin (Binary.power width)
  pack word = fromℕ< (Binary.valueBound word)

  unpack : ∀ width → Fin (Binary.power width) → Word width
  unpack width number = Binary.Expansion.digits (Binary.encode width (toℕ number) (toℕ<n number))

  packValue : ∀ {width} (word : Word width) → toℕ (pack word) ≡ Binary.value word
  packValue word = toℕ-fromℕ< (Binary.valueBound word)

  unpackValue : ∀ width number → Binary.value (unpack width number) ≡ toℕ number
  unpackValue width number = Binary.decodeEncode width (toℕ number) (toℕ<n number)

  unpackPack : ∀ {width} (word : Word width) → unpack width (pack word) ≡ word
  unpackPack {width} word = Binary.valueInjective _ word (trans (unpackValue width (pack word)) (packValue word))

  packUnpack : ∀ width number → pack (unpack width number) ≡ number
  packUnpack width number = toℕ-injective
    (trans (packValue (unpack width number)) (unpackValue width number))

Byte = Fin 256

packByte : Word 8 → Byte
packByte = pack

unpackByte : Byte → Word 8
unpackByte = unpack 8
