{-# OPTIONS --safe #-}
-- Invert numeric byte ranges into actual payload bits. The numeric decision
-- procedure is related to the previously proved bit classifier, rather than
-- replacing it with a second unchecked UTF-8 decoder.
module Mimir.UTF8ByteDecode where

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ; _<_; _≤_; _<?_; suc)
open import Data.Nat.Properties using (≤-trans; 1+n≰n; m≤m+n)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Mimir.Bits using (Byte; Word)
open import Mimir.UTF8ByteRanges using (Kind; single; continuation; two; three; four; invalid; Range; kind; classifiedRange)
import Mimir.UTF8Byte as B

choose : ℕ → Kind
choose n with n <? 128
... | yes below = single
... | no above with n <? 192
...   | yes below = continuation
...   | no above with n <? 224
...     | yes below = two
...     | no above with n <? 240
...       | yes below = three
...       | no above with n <? 248
...         | yes below = four
...         | no above = invalid

separated : ∀ {n threshold} → threshold ≤ n → n < threshold → ⊥
separated lower upper = 1+n≰n (≤-trans upper lower)

rangeChoice : ∀ tag n → Range tag n → choose n ≡ tag
rangeChoice single n (lower , upper) with n <? 128
... | yes inside = refl
... | no outside = ⊥-elim (outside (Data.Nat.s≤s upper))
rangeChoice continuation n (lower , upper) with n <? 128
... | yes outside = ⊥-elim (separated lower outside)
... | no above with n <? 192
...   | yes inside = refl
...   | no outside = ⊥-elim (outside (Data.Nat.s≤s upper))
rangeChoice two n (lower , upper) with n <? 128
... | yes outside = ⊥-elim (separated (≤-trans (m≤m+n 128 64) lower) outside)
... | no above with n <? 192
...   | yes outside = ⊥-elim (separated lower outside)
...   | no above with n <? 224
...     | yes inside = refl
...     | no outside = ⊥-elim (outside (Data.Nat.s≤s upper))
rangeChoice three n (lower , upper) with n <? 128
... | yes outside = ⊥-elim (separated (≤-trans (m≤m+n 128 96) lower) outside)
... | no above with n <? 192
...   | yes outside = ⊥-elim (separated (≤-trans (m≤m+n 192 32) lower) outside)
...   | no above with n <? 224
...     | yes outside = ⊥-elim (separated lower outside)
...     | no above with n <? 240
...       | yes inside = refl
...       | no outside = ⊥-elim (outside (Data.Nat.s≤s upper))
rangeChoice four n (lower , upper) with n <? 128
... | yes outside = ⊥-elim (separated (≤-trans (m≤m+n 128 112) lower) outside)
... | no above with n <? 192
...   | yes outside = ⊥-elim (separated (≤-trans (m≤m+n 192 48) lower) outside)
...   | no above with n <? 224
...     | yes outside = ⊥-elim (separated (≤-trans (m≤m+n 224 16) lower) outside)
...     | no above with n <? 240
...       | yes outside = ⊥-elim (separated lower outside)
...       | no above with n <? 248
...         | yes inside = refl
...         | no outside = ⊥-elim (outside (Data.Nat.s≤s upper))
rangeChoice invalid n (lower , upper) with n <? 128
... | yes outside = ⊥-elim (separated (≤-trans (m≤m+n 128 120) lower) outside)
... | no above with n <? 192
...   | yes outside = ⊥-elim (separated (≤-trans (m≤m+n 192 56) lower) outside)
...   | no above with n <? 224
...     | yes outside = ⊥-elim (separated (≤-trans (m≤m+n 224 24) lower) outside)
...     | no above with n <? 240
...       | yes outside = ⊥-elim (separated (≤-trans (m≤m+n 240 8) lower) outside)
...       | no above with n <? 248
...         | yes outside = ⊥-elim (separated lower outside)
...         | no above = refl

classifiedKind : ∀ tag byte → Range tag (toℕ byte) → kind (B.classify byte) ≡ tag
classifiedKind tag byte bounded = trans (sym (rangeChoice (kind (B.classify byte)) (toℕ byte) (classifiedRange byte)))
  (rangeChoice tag (toℕ byte) bounded)

record Payload (tag : Kind) (byte : Byte) : Set where
  constructor payload
  field actual : B.Tag; sameKind : kind actual ≡ tag; meaning : B.Meaning actual byte

read : ∀ tag byte → Range tag (toℕ byte) → Payload tag byte
read tag byte bounded = payload (B.classify byte) (classifiedKind tag byte bounded) (B.classifySound byte)

continuationPayload : ∀ byte → Range continuation (toℕ byte) → Σ (Word 6) (λ word → byte ≡ B.continuationByte word)
continuationPayload byte bounded with read continuation byte bounded
... | payload (B.continuation word) refl meaning = word , meaning

singlePayload : ∀ byte → Range single (toℕ byte) → Σ (Word 7) (λ word → byte ≡ B.singleByte word)
singlePayload byte bounded with read single byte bounded
... | payload (B.single word) refl meaning = word , meaning

twoPayload : ∀ byte → Range two (toℕ byte) → Σ (Word 5) (λ word → byte ≡ B.twoByte word)
twoPayload byte bounded with read two byte bounded
... | payload (B.leadingTwo word) refl meaning = word , meaning

threePayload : ∀ byte → Range three (toℕ byte) → Σ (Word 4) (λ word → byte ≡ B.threeByte word)
threePayload byte bounded with read three byte bounded
... | payload (B.leadingThree word) refl meaning = word , meaning

fourPayload : ∀ byte → Range four (toℕ byte) → Σ (Word 3) (λ word → byte ≡ B.fourByte word)
fourPayload byte bounded with read four byte bounded
... | payload (B.leadingFour word) refl meaning = word , meaning
