{-# OPTIONS --safe #-}
-- Correspondence between the public nonblank predicate and the implementation
-- rule !text.trim().is_empty(), for arbitrary Unicode scalar sequences.
module Mimir.TrimLaws where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.List using ([]; _∷_; _++_; reverse)
open import Data.List.Properties using (unfold-reverse)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import Mimir.Text

appendNonblank : ∀ left right → nonblank (left ++ right) ≡ nonblank left ∨ nonblank right
appendNonblank [] right = refl
appendNonblank (c ∷ cs) right with isWhitespace c
... | true = appendNonblank cs right
... | false = refl

trimStartNonblank : ∀ text → nonblank (trimStart text) ≡ nonblank text
trimStartNonblank [] = refl
trimStartNonblank (c ∷ cs) with isWhitespace c in whitespace
... | true = trimStartNonblank cs
... | false rewrite whitespace = refl

reverseNonblank : ∀ text → nonblank (reverse text) ≡ nonblank text
reverseNonblank [] = refl
reverseNonblank (c ∷ cs) rewrite unfold-reverse c cs |
  appendNonblank (reverse cs) (c ∷ []) | reverseNonblank cs
  with isWhitespace c in whitespace | nonblank cs in rest
... | true | true rewrite rest = refl
... | true | false rewrite rest = refl
... | false | true = refl
... | false | false = refl

trimPreservesNonblank : ∀ text → nonblank (trim text) ≡ nonblank text
trimPreservesNonblank text =
  trans (reverseNonblank (trimStart (reverse (trimStart text))))
    (trans (trimStartNonblank (reverse (trimStart text)))
      (trans (reverseNonblank (trimStart text)) (trimStartNonblank text)))

blankTrimStartEmpty : ∀ text → nonblank text ≡ false → trimStart text ≡ []
blankTrimStartEmpty [] proof = refl
blankTrimStartEmpty (c ∷ cs) proof with isWhitespace c
... | true = blankTrimStartEmpty cs proof
... | false with proof
...   | ()

blankTrimEmpty : ∀ text → nonblank text ≡ false → trim text ≡ []
blankTrimEmpty text proof rewrite blankTrimStartEmpty text proof = refl

nonblankNonempty : ∀ text → Nonblank text → Nonempty text
nonblankNonempty [] ()
nonblankNonempty (c ∷ cs) proof = cons c cs

nonblankTrimNonempty : ∀ text → Nonblank text → Nonempty (trim text)
nonblankTrimNonempty text proof = nonblankNonempty (trim text) (trans (trimPreservesNonblank text) proof)

trimNonemptyNonblank : ∀ text → Nonempty (trim text) → Nonblank text
trimNonemptyNonblank text present with nonblank text in blank
... | true = refl
... | false with subst Nonempty (blankTrimEmpty text blank) present
...   | ()
