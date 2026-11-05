{-# OPTIONS --safe #-}
-- Lexicographic scalar order. UTF-8 byte/scalar order correspondence is a
-- separate codec theorem; this module does not assume that theorem.
module Mimir.TextOrder where

open import Data.Char using (toℕ)
open import Data.List using (map)
import Data.Nat as N
import Data.Nat.Properties as N
import Data.List.Relation.Binary.Lex.Strict as Lex
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; sym)
open import Mimir.Text using (Text)

_≤Text_ : Text → Text → Set
left ≤Text right = Lex.Lex-≤ _≡_ N._<_ (map toℕ left) (map toℕ right)

_≤Text?_ : ∀ left right → Dec (left ≤Text right)
left ≤Text? right = Lex.≤-decidable N._≟_ N._<?_ (map toℕ left) (map toℕ right)

notReverseImpliesForward : ∀ left right → ¬ (right ≤Text left) → left ≤Text right
notReverseImpliesForward left right notReverse with Lex.≤-total sym N.<-cmp (map toℕ left) (map toℕ right)
... | inj₁ forward = forward
... | inj₂ reverse = ⊥-elim (notReverse reverse)
