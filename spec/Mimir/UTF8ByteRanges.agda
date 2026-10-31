{-# OPTIONS --safe #-}
-- Numeric ranges follow from the actual prefix bits for every byte, without
-- an enumerated test set or an assumption about the classifier.
module Mimir.UTF8ByteRanges where

open import Data.Vec using ([]; _∷_)
open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ; suc; _+_; _≤_; _<_; s≤s⁻¹)
open import Data.Nat.Properties using (m≤n+m; +-monoˡ-<)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Mimir.Bits using (Byte; Word; O; I; unpackByte; unpackValue)
import Mimir.Bits as Bits
import Mimir.UTF8Byte as B

Between : ℕ → ℕ → ℕ → Set
Between lower upper number = lower ≤ number × number ≤ upper

data Kind : Set where single continuation two three four invalid : Kind

kind : B.Tag → Kind
kind (B.single payload) = single
kind (B.continuation payload) = continuation
kind (B.leadingTwo payload) = two
kind (B.leadingThree payload) = three
kind (B.leadingFour payload) = four
kind B.invalid = invalid

Range : Kind → ℕ → Set
Range single = Between 0 127
Range continuation = Between 128 191
Range two = Between 192 223
Range three = Between 224 239
Range four = Between 240 247
Range invalid = Between 248 255

Numeric : B.Tag → ℕ → Set
Numeric tag = Range (kind tag)

offsetRange : ∀ {width} (word : Word width) offset upper →
  Bits.Binary.power width + offset ≡ suc upper → Between offset upper (Bits.Binary.value word + offset)
offsetRange word offset upper top = m≤n+m offset (Bits.Binary.value word) ,
  s≤s⁻¹ (subst (suc (Bits.Binary.value word + offset) ≤_) top
    (+-monoˡ-< offset (Bits.Binary.valueBound word)))

bitsRange : ∀ word → Numeric (B.classifyBits word) (Bits.Binary.value word)
bitsRange (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ O ∷ [])
  rewrite Bits.Binary.valueAppend (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ []) (O ∷ []) =
  offsetRange (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ []) 0 127 refl
bitsRange (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ O ∷ I ∷ [])
  rewrite Bits.Binary.valueAppend (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ []) (O ∷ I ∷ []) =
  offsetRange (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ []) 128 191 refl
bitsRange (a ∷ b ∷ c ∷ d ∷ e ∷ O ∷ I ∷ I ∷ [])
  rewrite Bits.Binary.valueAppend (a ∷ b ∷ c ∷ d ∷ e ∷ []) (O ∷ I ∷ I ∷ []) =
  offsetRange (a ∷ b ∷ c ∷ d ∷ e ∷ []) 192 223 refl
bitsRange (a ∷ b ∷ c ∷ d ∷ O ∷ I ∷ I ∷ I ∷ [])
  rewrite Bits.Binary.valueAppend (a ∷ b ∷ c ∷ d ∷ []) (O ∷ I ∷ I ∷ I ∷ []) =
  offsetRange (a ∷ b ∷ c ∷ d ∷ []) 224 239 refl
bitsRange (a ∷ b ∷ c ∷ O ∷ I ∷ I ∷ I ∷ I ∷ [])
  rewrite Bits.Binary.valueAppend (a ∷ b ∷ c ∷ []) (O ∷ I ∷ I ∷ I ∷ I ∷ []) =
  offsetRange (a ∷ b ∷ c ∷ []) 240 247 refl
bitsRange (a ∷ b ∷ c ∷ I ∷ I ∷ I ∷ I ∷ I ∷ [])
  rewrite Bits.Binary.valueAppend (a ∷ b ∷ c ∷ []) (I ∷ I ∷ I ∷ I ∷ I ∷ []) =
  offsetRange (a ∷ b ∷ c ∷ []) 248 255 refl

classifiedRange : ∀ byte → Numeric (B.classify byte) (toℕ byte)
classifiedRange byte = subst (Numeric (B.classify byte)) (unpackValue 8 byte) (bitsRange (unpackByte byte))
