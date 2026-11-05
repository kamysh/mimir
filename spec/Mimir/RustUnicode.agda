{-# OPTIONS --safe #-}
-- Unicode 17.0.0 classification from the pinned Rust 1.99.0 source tables.
-- Every table entry participates in the checked metadata certificate.
-- Binary-search/packed-header machine correspondence remains separate.
module Mimir.RustUnicode where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Char using (Char; toℕ)
open import Data.List.Relation.Unary.All using (all?)
open import Data.List.Relation.Unary.Any using (any?)
open import Data.Nat using (ℕ; _≤_; _<_; _≤?_; _<?_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no; does)
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.UnicodeSkipSearch as Skip
open import Mimir.RustUnicodeData

abstract
  alphabeticCertified : Skip.Certified alphabeticHeaders alphabeticOffsets
  alphabeticCertified = Skip.certified
    (toWitness {a? = all? (_<? 256) alphabeticOffsets} tt)
    (toWitness {a? = all? (Skip.headerBounds? alphabeticOffsets) alphabeticHeaders} tt)
    (toWitness {a? = Skip.increasing? alphabeticHeaders} tt)
    (toWitness {a? = any? (λ entry → 1114111 <? Skip.endpoint entry) alphabeticHeaders} tt)

  numericCertified : Skip.Certified numericHeaders numericOffsets
  numericCertified = Skip.certified
    (toWitness {a? = all? (_<? 256) numericOffsets} tt)
    (toWitness {a? = all? (Skip.headerBounds? numericOffsets) numericHeaders} tt)
    (toWitness {a? = Skip.increasing? numericHeaders} tt)
    (toWitness {a? = any? (λ entry → 1114111 <? Skip.endpoint entry) numericHeaders} tt)

alphabeticSelection : ∀ needle → needle ≤ 1114111 → Skip.Selection needle alphabeticHeaders alphabeticOffsets
alphabeticSelection needle bounded = Skip.select needle alphabeticHeaders alphabeticOffsets bounded alphabeticCertified

numericSelection : ∀ needle → needle ≤ 1114111 → Skip.Selection needle numericHeaders numericOffsets
numericSelection needle bounded = Skip.select needle numericHeaders numericOffsets bounded numericCertified

between : ℕ → ℕ → ℕ → Bool
between low high number with low ≤? number | number ≤? high
... | yes lower | yes upper = true
... | _ | _ = false

betweenTrue : ∀ low high number → low ≤ number → number ≤ high → between low high number ≡ true
betweenTrue low high number lower upper with low ≤? number | number ≤? high
... | yes acceptedLow | yes acceptedHigh = refl
... | no rejected | _ = ⊥-elim (rejected lower)
... | yes acceptedLow | no rejected = ⊥-elim (rejected upper)

betweenSound : ∀ low high number → between low high number ≡ true → low ≤ number × number ≤ high
betweenSound low high number accepted with low ≤? number | number ≤? high
... | yes lower | yes upper = lower , upper
betweenSound low high number () | no lower | _
betweenSound low high number () | yes lower | no upper

asciiAlphanumeric : ℕ → Bool
asciiAlphanumeric number = between 97 122 number ∨ between 65 90 number ∨ between 48 57 number

alphabetic numeric : ℕ → Bool
alphabetic number with 170 ≤? number
... | no low = false
... | yes high = Skip.lookup number alphabeticHeaders alphabeticOffsets
numeric number with 178 ≤? number
... | no low = false
... | yes high = Skip.lookup number numericHeaders numericOffsets

alphanumeric : ℕ → Bool
alphanumeric number with asciiAlphanumeric number
... | true = true
... | false with number ≤? 169
...   | yes low = false
...   | no high = alphabetic number ∨ numeric number

isAlphanumeric : Char → Bool
isAlphanumeric char = alphanumeric (toℕ char)

asciiAccepted : ∀ number → asciiAlphanumeric number ≡ true → alphanumeric number ≡ true
asciiAccepted number accepted rewrite accepted = refl

lowNonAsciiRefused : ∀ number → asciiAlphanumeric number ≡ false → number ≤ 169 → alphanumeric number ≡ false
lowNonAsciiRefused number notAscii lower rewrite notAscii with number ≤? 169
... | yes low = refl
... | no high = ⊥-elim (high lower)
