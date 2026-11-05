{-# OPTIONS --safe #-}
-- Maximal prefix splitting by an arbitrary decidable character predicate.
-- No input character is normalized or discarded by the split itself.
module Mimir.TextFields where

open import Data.Char using (Char)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Mimir.Text using (Text)

module Split (Separator : Char → Set) (separator? : (c : Char) → Dec (Separator c)) where
  Boundary : Text → Set
  Boundary [] = ⊤
  Boundary (c ∷ cs) = Separator c

  record Cut (input : Text) : Set where
    constructor cut
    field
      prefix suffix : Text
      exact : input ≡ prefix ++ suffix
      noSeparator : All (λ c → ¬ Separator c) prefix
      boundary : Boundary suffix

  split : ∀ input → Cut input
  split [] = cut [] [] refl [] tt
  split (c ∷ cs) with separator? c
  ... | yes separator = cut [] (c ∷ cs) refl [] separator
  ... | no notSeparator with split cs
  ...   | cut before after exact none boundary = cut (c ∷ before) after
      (cong (c ∷_) exact) (notSeparator ∷ none) boundary

  atBoundary : ∀ input → Boundary input → Cut.prefix (split input) ≡ [] × Cut.suffix (split input) ≡ input
  atBoundary [] boundary = refl , refl
  atBoundary (c ∷ cs) boundary with separator? c
  ... | yes _ = refl , refl
  ... | no notSeparator = ⊥-elim (notSeparator boundary)

  maximalSplit : ∀ before after → All (λ c → ¬ Separator c) before → Boundary after →
    Cut.prefix (split (before ++ after)) ≡ before × Cut.suffix (split (before ++ after)) ≡ after
  maximalSplit [] after [] boundary = atBoundary after boundary
  maximalSplit (c ∷ cs) after (notSeparator ∷ rest) boundary with separator? c
  ... | yes separator = ⊥-elim (notSeparator separator)
  ... | no _ with split (cs ++ after) | maximalSplit cs after rest boundary
  ...   | cut prefix suffix exact none ended | prefixEqual , suffixEqual =
      cong (c ∷_) prefixEqual , suffixEqual

  splitRetainsEverything : ∀ input → input ≡ Cut.prefix (split input) ++ Cut.suffix (split input)
  splitRetainsEverything input = Cut.exact (split input)
