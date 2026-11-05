{-# OPTIONS --safe #-}
module Mimir.WhitespaceCut where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Mimir.Text using (Text; isWhitespace; trimStart)

Boundary : Text → Set
Boundary [] = ⊤
Boundary (char ∷ rest) = isWhitespace char ≡ false

record Cut (input : Text) : Set where
  constructor cutAt
  field
    spaces rest : Text
    exact : input ≡ spaces ++ rest
    whitespace : All (λ char → isWhitespace char ≡ true) spaces
    boundary : Boundary rest
    trimmed : rest ≡ trimStart input

nonwhiteStep : ∀ char input → isWhitespace char ≡ false → trimStart (char ∷ input) ≡ char ∷ input
nonwhiteStep char input observed rewrite observed = refl

whiteStep : ∀ char input → isWhitespace char ≡ true → trimStart (char ∷ input) ≡ trimStart input
whiteStep char input observed rewrite observed = refl

cut : ∀ input → Cut input
cut [] = cutAt [] [] refl [] tt refl
cut (char ∷ input) with isWhitespace char in observed
... | false = cutAt [] (char ∷ input) refl [] observed (sym (nonwhiteStep char input observed))
... | true with cut input
...   | cutAt spaces rest exact whitespace boundary trimmed =
  cutAt (char ∷ spaces) rest (cong (char ∷_) exact) (observed ∷ whitespace) boundary
    (trans trimmed (sym (whiteStep char input observed)))
