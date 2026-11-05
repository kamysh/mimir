{-# OPTIONS --safe #-}
-- Winnow 0.6.26's mixed byte/scalar error-column calculation. At EOF it
-- clamps to the final byte before adding the offset beyond that byte; this
-- deliberately differs from a simple line/column scan of the whole prefix.
module Mimir.WinnowPosition where

open import Data.List using (List; []; _∷_; length; take; drop)
open import Data.List.Properties using (length-take)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊓_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans; m⊓n≤m; m⊓n≤n)
open import Data.Fin using (#_; _≟_)
open import Data.Maybe using (nothing; just)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Mimir.Bits using (Byte)
import Mimir.JsonPosition as Lines
import Mimir.UTF8Text as UTF8

startBound : ∀ input → Lines.start input ≤ length input
startBound [] = z≤n
startBound (byte ∷ rest) with Lines.lastBreak rest | startBound rest
... | just offset | bounded = s≤s bounded
... | nothing | bounded with byte ≟ (# 10)
...   | yes newline = s≤s z≤n
...   | no other = z≤n

prefixStartBound : ∀ input index → Lines.start (take index input) ≤ index
prefixStartBound input index = ≤-trans (startBound (take index input))
  (subst (_≤ index) (sym (length-take index input)) (m⊓n≤m index (length input)))

sliceColumn : List Byte → ℕ → ℕ → ℕ
sliceColumn input lineStart index with UTF8.decode (take (suc index ∸ lineStart) (drop lineStart input))
... | inj₁ malformed = index ∸ lineStart
... | inj₂ parsedText = length (UTF8.Decoded.values parsedText) ∸ 1

record Location : Set where
  constructor location
  field line column : ℕ

translate : List Byte → ℕ → Location
translate [] index = location 0 index
translate input@(_ ∷ rest) index = location (Lines.newlines (take lineStart input))
  (sliceColumn input lineStart safeIndex + (index ∸ safeIndex))
  where
  safeIndex = index ⊓ length rest
  lineStart = Lines.start (take safeIndex input)

safeIndexBeforeEnd : ∀ (byte : Byte) (rest : List Byte) index → index ⊓ length rest < length (byte ∷ rest)
safeIndexBeforeEnd byte rest index = s≤s (m⊓n≤n index (length rest))

clampedBeforeOffset : ∀ (rest : List Byte) index → index ⊓ length rest ≤ index
clampedBeforeOffset rest index = m⊓n≤m index (length rest)

sliceStartBeforeEnd : ∀ byte rest index → Lines.start (take (index ⊓ length rest) (byte ∷ rest)) < length (byte ∷ rest)
sliceStartBeforeEnd byte rest index = Data.Nat.Properties.≤-<-trans
  (prefixStartBound (byte ∷ rest) (index ⊓ length rest)) (safeIndexBeforeEnd byte rest index)

validPrefixUsesScalars : ∀ input lineStart index parsedText →
  UTF8.decode (take (suc index ∸ lineStart) (drop lineStart input)) ≡ inj₂ parsedText →
  sliceColumn input lineStart index ≡ length (UTF8.Decoded.values parsedText) ∸ 1
validPrefixUsesScalars input lineStart index parsedText observed rewrite observed = refl

incompleteScalarUsesBytes : ∀ input lineStart index malformed →
  UTF8.decode (take (suc index ∸ lineStart) (drop lineStart input)) ≡ inj₁ malformed →
  sliceColumn input lineStart index ≡ index ∸ lineStart
incompleteScalarUsesBytes input lineStart index malformed observed rewrite observed = refl

data Nonempty {A : Set} : List A → Set where
  more : ∀ entry rest → Nonempty (entry ∷ rest)

sliceNonempty : ∀ {A : Set} (input : List A) begin index → begin ≤ index → index < length input →
  Nonempty (take (suc index ∸ begin) (drop begin input))
sliceNonempty [] begin index lower ()
sliceNonempty (entry ∷ rest) zero index lower bounded = more entry (take index rest)
sliceNonempty (entry ∷ rest) (suc begin) zero () bounded
sliceNonempty (entry ∷ rest) (suc begin) (suc index) (s≤s lower) (s≤s bounded) = sliceNonempty rest begin index lower bounded

translatedSliceNonempty : ∀ byte rest offset →
  Nonempty (take (suc (offset ⊓ length rest) ∸ Lines.start (take (offset ⊓ length rest) (byte ∷ rest)))
    (drop (Lines.start (take (offset ⊓ length rest) (byte ∷ rest))) (byte ∷ rest)))
translatedSliceNonempty byte rest offset = sliceNonempty (byte ∷ rest) _ _
  (prefixStartBound (byte ∷ rest) (offset ⊓ length rest)) (safeIndexBeforeEnd byte rest offset)

nonemptyNotNil : ∀ {A : Set} {input : List A} → Nonempty input → input ≡ [] → Data.Empty.⊥
nonemptyNotNil (more entry rest) ()

decodedNonempty : ∀ input → Nonempty input → (parsedText : UTF8.Decoded input) → Nonempty (UTF8.Decoded.values parsedText)
decodedNonempty input nonempty (UTF8.decoded [] exact) = ⊥-elim (nonemptyNotNil nonempty exact)
decodedNonempty input nonempty (UTF8.decoded (value ∷ rest) exact) = more value rest

decodedCountPositive : ∀ input → Nonempty input → (parsedText : UTF8.Decoded input) → 1 ≤ length (UTF8.Decoded.values parsedText)
decodedCountPositive input nonempty parsedText with decodedNonempty input nonempty parsedText
... | more value rest = s≤s z≤n
