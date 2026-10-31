{-# OPTIONS --safe #-}
-- All 256 bytes classified by their actual prefix bits. Scalar-range and
-- shortest-form checks belong to the assembled packet, not this classifier.
module Mimir.UTF8Byte where

open import Data.Vec using ([]; _∷_; _++_)
open import Data.Fin using (toℕ)
open import Data.Nat using (_+_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; trans)
open import Mimir.Bits

data Tag : Set where
  single : Word 7 → Tag
  continuation : Word 6 → Tag
  leadingTwo : Word 5 → Tag
  leadingThree : Word 4 → Tag
  leadingFour : Word 3 → Tag
  invalid : Tag

classifyBits : Word 8 → Tag
classifyBits (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ O ∷ []) = single (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ [])
classifyBits (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ O ∷ I ∷ []) = continuation (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ [])
classifyBits (a ∷ b ∷ c ∷ d ∷ e ∷ O ∷ I ∷ I ∷ []) = leadingTwo (a ∷ b ∷ c ∷ d ∷ e ∷ [])
classifyBits (a ∷ b ∷ c ∷ d ∷ O ∷ I ∷ I ∷ I ∷ []) = leadingThree (a ∷ b ∷ c ∷ d ∷ [])
classifyBits (a ∷ b ∷ c ∷ O ∷ I ∷ I ∷ I ∷ I ∷ []) = leadingFour (a ∷ b ∷ c ∷ [])
classifyBits (a ∷ b ∷ c ∷ I ∷ I ∷ I ∷ I ∷ I ∷ []) = invalid

classify : Byte → Tag
classify byte = classifyBits (unpackByte byte)

singleByte : Word 7 → Byte
singleByte payload = packByte (payload ++ (O ∷ []))

continuationByte : Word 6 → Byte
continuationByte payload = packByte (payload ++ (O ∷ I ∷ []))

twoByte : Word 5 → Byte
twoByte payload = packByte (payload ++ (O ∷ I ∷ I ∷ []))

threeByte : Word 4 → Byte
threeByte payload = packByte (payload ++ (O ∷ I ∷ I ∷ I ∷ []))

fourByte : Word 3 → Byte
fourByte payload = packByte (payload ++ (O ∷ I ∷ I ∷ I ∷ I ∷ []))

singleRoundTrip : ∀ payload → classify (singleByte payload) ≡ single payload
singleRoundTrip (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ [])
  rewrite unpackPack (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ O ∷ []) = refl

continuationRoundTrip : ∀ payload → classify (continuationByte payload) ≡ continuation payload
continuationRoundTrip (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ [])
  rewrite unpackPack (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ O ∷ I ∷ []) = refl

twoRoundTrip : ∀ payload → classify (twoByte payload) ≡ leadingTwo payload
twoRoundTrip (a ∷ b ∷ c ∷ d ∷ e ∷ [])
  rewrite unpackPack (a ∷ b ∷ c ∷ d ∷ e ∷ O ∷ I ∷ I ∷ []) = refl

threeRoundTrip : ∀ payload → classify (threeByte payload) ≡ leadingThree payload
threeRoundTrip (a ∷ b ∷ c ∷ d ∷ [])
  rewrite unpackPack (a ∷ b ∷ c ∷ d ∷ O ∷ I ∷ I ∷ I ∷ []) = refl

fourRoundTrip : ∀ payload → classify (fourByte payload) ≡ leadingFour payload
fourRoundTrip (a ∷ b ∷ c ∷ [])
  rewrite unpackPack (a ∷ b ∷ c ∷ O ∷ I ∷ I ∷ I ∷ I ∷ []) = refl

Meaning : Tag → Byte → Set
Meaning (single payload) byte = byte ≡ singleByte payload
Meaning (continuation payload) byte = byte ≡ continuationByte payload
Meaning (leadingTwo payload) byte = byte ≡ twoByte payload
Meaning (leadingThree payload) byte = byte ≡ threeByte payload
Meaning (leadingFour payload) byte = byte ≡ fourByte payload
Meaning invalid byte = ⊤

bitsSound : ∀ word → Meaning (classifyBits word) (packByte word)
bitsSound (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ O ∷ []) = refl
bitsSound (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ O ∷ I ∷ []) = refl
bitsSound (a ∷ b ∷ c ∷ d ∷ e ∷ O ∷ I ∷ I ∷ []) = refl
bitsSound (a ∷ b ∷ c ∷ d ∷ O ∷ I ∷ I ∷ I ∷ []) = refl
bitsSound (a ∷ b ∷ c ∷ O ∷ I ∷ I ∷ I ∷ I ∷ []) = refl
bitsSound (a ∷ b ∷ c ∷ I ∷ I ∷ I ∷ I ∷ I ∷ []) = tt

classifySound : ∀ byte → Meaning (classify byte) byte
classifySound byte = subst (Meaning (classify byte)) (packUnpack 8 byte) (bitsSound (unpackByte byte))

abstract
  singleNumeric : ∀ payload → toℕ (singleByte payload) ≡ Binary.value payload
  singleNumeric payload rewrite packValue (payload ++ (O ∷ [])) |
    Binary.valueAppend payload (O ∷ []) = +-identityʳ (Binary.value payload)

  continuationNumeric : ∀ payload → toℕ (continuationByte payload) ≡ Binary.value payload + 128
  continuationNumeric payload rewrite packValue (payload ++ (O ∷ I ∷ [])) |
    Binary.valueAppend payload (O ∷ I ∷ []) = refl

  twoNumeric : ∀ payload → toℕ (twoByte payload) ≡ Binary.value payload + 192
  twoNumeric payload rewrite packValue (payload ++ (O ∷ I ∷ I ∷ [])) |
    Binary.valueAppend payload (O ∷ I ∷ I ∷ []) = refl

  threeNumeric : ∀ payload → toℕ (threeByte payload) ≡ Binary.value payload + 224
  threeNumeric payload rewrite packValue (payload ++ (O ∷ I ∷ I ∷ I ∷ [])) |
    Binary.valueAppend payload (O ∷ I ∷ I ∷ I ∷ []) = refl

  fourNumeric : ∀ payload → toℕ (fourByte payload) ≡ Binary.value payload + 240
  fourNumeric payload rewrite packValue (payload ++ (O ∷ I ∷ I ∷ I ∷ I ∷ [])) |
    Binary.valueAppend payload (O ∷ I ∷ I ∷ I ∷ I ∷ []) = refl
