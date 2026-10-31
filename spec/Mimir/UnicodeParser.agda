{-# OPTIONS --safe #-}
-- Exact-consumption cursors carry scalar validity through every continuation.
-- Recoverable repetition restores both the input and its admission evidence.
module Mimir.UnicodeParser where

open import Data.Char using (toℕ)
open import Data.List using ([]; _∷_; length)
open import Data.Nat using (zero; suc; _<_; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Mimir.Text using (Text)
import Mimir.UnicodeScalar as Scalar
import Mimir.UnicodeText as Unicode
import Mimir.TextPredicatePreservation as Preservation
import Mimir.MigrationSyntax as Syntax

module Raw = Syntax.P
open Raw using (Result; success; failure; backtrack; repeatNoProgress; done; reframe; prefix; mapResult)
module Keep = Preservation.Preserve (λ char → Scalar.Valid (toℕ char))

Parser : Set → Set
Parser A = ∀ input → Unicode.Valid input → Result A input

remainingValid : ∀ {A input} (result : Result A input) → Unicode.Valid input → Unicode.Valid (Raw.remaining result)
remainingValid result valid = Keep.suffix _ (Raw.consumed result) (Raw.remaining result) (Raw.reconstruct result) valid

lift : ∀ {A} → Raw.Parser A → Parser A
lift parser input valid = parser input

bindResult : ∀ {A B input} (result : Result A input) → Unicode.Valid input → (A → Parser B) → Result B input
bindResult (failure code before after exact) valid next = failure code before after exact
bindResult result@(success value before after exact) valid next =
  reframe exact (prefix before (next value after (remainingValid result valid)))

bind : ∀ {A B} → Parser A → (A → Parser B) → Parser B
bind first next input valid = bindResult (first input valid) valid next

repeatBounded : ∀ {A} (parser : Parser A) fuel input → Unicode.Valid input → length input < fuel → Result (Data.List.List A) input
repeatBounded parser zero input valid ()
repeatBounded parser (suc fuel) input valid bounded with parser input valid
... | failure (backtrack error) before after exact = done [] input
... | failure code before after exact = failure code before after exact
... | success value [] after exact = failure repeatNoProgress [] after exact
... | result@(success value (char ∷ before) after exact) =
  reframe exact (prefix (char ∷ before) (mapResult (value ∷_)
    (repeatBounded parser fuel after (remainingValid result valid)
      (Raw.strictSuffix fuel input char before after exact bounded))))

repeat : ∀ {A} → Parser A → Parser (Data.List.List A)
repeat parser input valid = repeatBounded parser (suc (length input)) input valid (s≤s ≤-refl)
