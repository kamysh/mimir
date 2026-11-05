{-# OPTIONS --safe #-}
-- Rust char::is_control uses exactly C0 and C1. The judge removes those
-- characters before applying a scalar-count limit; this is not a byte limit.
module Mimir.DiagnosticText where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char; toℕ)
open import Data.List using (List; []; _∷_; length; take)
open import Data.List.Properties using (length-take; take-all)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as All
open import Data.Nat using (ℕ; zero; suc; _≤_; _≤?_; _+_; _*_; z≤n; s≤s)
open import Data.Nat.Properties using (m⊓n≤m; ≤-refl; ≤-trans; +-mono-≤; *-monoʳ-≤; *-suc)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym; trans)
import Mimir.Text as Text

control : Char → Bool
control character with toℕ character ≤? 31
... | yes c0 = true
... | no notC0 with 127 ≤? toℕ character
...   | no beforeC1 = false
...   | yes afterStart with toℕ character ≤? 159
...     | yes c1 = true
...     | no afterC1 = false

NonControl : Char → Set
NonControl character = control character ≡ false

strip : List Char → List Char
strip [] = []
strip (character ∷ rest) with control character
... | true = strip rest
... | false = character ∷ strip rest

bounded : ℕ → List Char → List Char
bounded limit text = take limit (strip text)

stripNonControl : ∀ text → All NonControl (strip text)
stripNonControl [] = []
stripNonControl (character ∷ rest) with control character in classified
... | true = stripNonControl rest
... | false = classified ∷ stripNonControl rest

stripIdentity : ∀ text → All NonControl text → strip text ≡ text
stripIdentity [] [] = refl
stripIdentity (character ∷ rest) (ordinary ∷ nonControl) rewrite ordinary = cong (character ∷_) (stripIdentity rest nonControl)

boundedNonControl : ∀ limit text → All NonControl (bounded limit text)
boundedNonControl limit text = All.take⁺ limit (stripNonControl text)

scalarBound : ∀ limit text → length (bounded limit text) ≤ limit
scalarBound limit text = subst (_≤ limit) (sym (length-take limit (strip text))) (m⊓n≤m limit (length (strip text)))

boundedIdentity : ∀ limit text → All NonControl text → length text ≤ limit → bounded limit text ≡ text
boundedIdentity limit text nonControl fits rewrite stripIdentity text nonControl = take-all limit text fits

idempotent : ∀ limit text → bounded limit (bounded limit text) ≡ bounded limit text
idempotent limit text = boundedIdentity limit (bounded limit text) (boundedNonControl limit text) (scalarBound limit text)

-- An independent subsequence relation records which original characters
-- survive and their order; truncation cannot introduce replacement text.
data Subsequence : List Char → List Char → Set where
  empty : ∀ source → Subsequence [] source
  keep : ∀ character {output source} → Subsequence output source → Subsequence (character ∷ output) (character ∷ source)
  skip : ∀ character {output source} → Subsequence output source → Subsequence output (character ∷ source)

stripSubsequence : ∀ text → Subsequence (strip text) text
stripSubsequence [] = empty []
stripSubsequence (character ∷ rest) with control character
... | true = skip character (stripSubsequence rest)
... | false = keep character (stripSubsequence rest)

takeSubsequence : ∀ limit {output source} → Subsequence output source → Subsequence (take limit output) source
takeSubsequence zero proof = empty _
takeSubsequence (suc limit) (empty source) = empty source
takeSubsequence (suc limit) (keep character proof) = keep character (takeSubsequence limit proof)
takeSubsequence (suc limit) (skip character proof) = skip character (takeSubsequence (suc limit) proof)

preservesOrder : ∀ limit text → Subsequence (bounded limit text) text
preservesOrder limit text = takeSubsequence limit (stripSubsequence text)

widthBound : ∀ character → Text.width character ≤ 4
widthBound character with toℕ character ≤? 127
... | yes ascii = s≤s z≤n
... | no nonASCII with toℕ character ≤? 2047
...   | yes two = s≤s (s≤s z≤n)
...   | no aboveTwo with toℕ character ≤? 65535
...     | yes three = s≤s (s≤s (s≤s z≤n))
...     | no four = ≤-refl

byteBoundByScalars : ∀ text → Text.byteLength text ≤ 4 * length text
byteBoundByScalars [] = z≤n
byteBoundByScalars (character ∷ rest) = subst (Text.byteLength (character ∷ rest) ≤_)
  (sym (*-suc 4 (length rest))) (+-mono-≤ (widthBound character) (byteBoundByScalars rest))

byteBound : ∀ limit text → Text.byteLength (bounded limit text) ≤ 4 * limit
byteBound limit text = ≤-trans (byteBoundByScalars (bounded limit text)) (*-monoʳ-≤ 4 (scalarBound limit text))
