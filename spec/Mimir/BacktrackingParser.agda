{-# OPTIONS --safe #-}
-- Winnow-style ordered alternatives, repetition and separated lists over
-- exact-consumption cursors. Recovery restores the checkpoint; fatal errors
-- retain the final cursor. All recursion is bounded by proved consumption.
module Mimir.BacktrackingParser where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++-≤ʳ)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; s≤s; s≤s⁻¹)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
import Mimir.SequenceCursor as Sequence

module Parsers (Atom Error Needed : Set) (merge : Error → Error → Error)
  (appendAlternative : Error → Error) where

  data Failure : Set where
    backtrack cut : Error → Failure
    incomplete : Needed → Failure
    repeatNoProgress separatorNoProgress : Failure

  module C = Sequence.Over Atom Failure
  open C public
  Input = List Atom

  Parser : Set → Set
  Parser A = (input : Input) → Result A input

  mapResult : ∀ {A B input} → (A → B) → Result A input → Result B input
  mapResult transform (success value consumed remaining exact) = success (transform value) consumed remaining exact
  mapResult transform (failure code consumed remaining exact) = failure code consumed remaining exact

  alternativeResult : ∀ {A input} → Error → Result A input → Result A input
  alternativeResult first (failure (backtrack second) consumed remaining exact) =
    failure (backtrack (appendAlternative (merge first second))) consumed remaining exact
  alternativeResult first result = result

  alternative : ∀ {A} → Parser A → Parser A → Parser A
  alternative first second input with first input
  ... | failure (backtrack error) consumed remaining exact = alternativeResult error (second input)
  ... | result = result

  strictSuffix : ∀ fuel (input : Input) (char : Atom) (consumed remaining : Input) →
    input ≡ (char ∷ consumed) ++ remaining → length input < suc fuel → length remaining < fuel
  strictSuffix fuel .((char ∷ consumed) ++ remaining) char consumed remaining refl bounded =
    ≤-trans (s≤s (length-++-≤ʳ remaining {xs = consumed})) (s≤s⁻¹ bounded)

  repeatBounded : ∀ {A} (parser : Parser A) fuel input → length input < fuel → Result (List A) input
  repeatBounded parser zero input ()
  repeatBounded parser (suc fuel) input bounded with parser input
  ... | failure (backtrack error) consumed remaining exact = done [] input
  ... | failure code consumed remaining exact = failure code consumed remaining exact
  ... | success value [] remaining exact = failure repeatNoProgress [] remaining exact
  ... | success value (char ∷ consumed) remaining exact =
    reframe exact (prefix (char ∷ consumed) (mapResult (value ∷_)
      (repeatBounded parser fuel remaining (strictSuffix fuel input char consumed remaining exact bounded))))

  repeat : ∀ {A} → Parser A → Parser (List A)
  repeat parser input = repeatBounded parser (suc (length input)) input (s≤s ≤-refl)

  separatorThen : ∀ {A B} → Parser A → Parser B → Parser A
  separatorThen element separator input with separator input
  ... | failure code consumed remaining exact = failure code consumed remaining exact
  ... | success ignored [] remaining exact = failure separatorNoProgress [] remaining exact
  ... | success ignored (char ∷ consumed) remaining exact =
    reframe exact (prefix (char ∷ consumed) (element remaining))

  separated : ∀ {A B} → Parser A → Parser B → Parser (List A)
  separated element separator input with element input
  ... | failure (backtrack error) consumed remaining exact = done [] input
  ... | failure code consumed remaining exact = failure code consumed remaining exact
  ... | success value consumed remaining exact =
    reframe exact (prefix consumed (mapResult (value ∷_) (repeat (separatorThen element separator) remaining)))

  alternativeRestartsAtOriginal : ∀ {A} (first second : Parser A) input error consumed remaining exact →
    first input ≡ failure (backtrack error) consumed remaining exact →
    alternative first second input ≡ alternativeResult error (second input)
  alternativeRestartsAtOriginal first second input error consumed remaining exact observed rewrite observed = refl

  cutDoesNotTryAlternative : ∀ {A} (first second : Parser A) input error consumed remaining exact →
    first input ≡ failure (cut error) consumed remaining exact →
    alternative first second input ≡ failure (cut error) consumed remaining exact
  cutDoesNotTryAlternative first second input error consumed remaining exact observed rewrite observed = refl

  incompleteDoesNotTryAlternative : ∀ {A} (first second : Parser A) input needed consumed remaining exact →
    first input ≡ failure (incomplete needed) consumed remaining exact →
    alternative first second input ≡ failure (incomplete needed) consumed remaining exact
  incompleteDoesNotTryAlternative first second input needed consumed remaining exact observed rewrite observed = refl

  repeatRestoresFailedAttempt : ∀ {A} (parser : Parser A) fuel input bounded error consumed remaining exact →
    parser input ≡ failure (backtrack error) consumed remaining exact →
    repeatBounded parser (suc fuel) input bounded ≡ done [] input
  repeatRestoresFailedAttempt parser fuel input bounded error consumed remaining exact observed rewrite observed = refl

  repeatKeepsFatalCursor : ∀ {A} (parser : Parser A) fuel input bounded error consumed remaining exact →
    parser input ≡ failure (cut error) consumed remaining exact →
    repeatBounded parser (suc fuel) input bounded ≡ failure (cut error) consumed remaining exact
  repeatKeepsFatalCursor parser fuel input bounded error consumed remaining exact observed rewrite observed = refl

  missingFirstItemRestoresInput : ∀ {A B} (element : Parser A) (separator : Parser B)
    input error consumed remaining exact → element input ≡ failure (backtrack error) consumed remaining exact →
    separated element separator input ≡ done [] input
  missingFirstItemRestoresInput element separator input error consumed remaining exact observed rewrite observed = refl

  emptySeparatorStopsBeforeElement : ∀ {A B} (element : Parser A) (separator : Parser B)
    input ignored remaining exact → separator input ≡ success ignored [] remaining exact →
    separatorThen element separator input ≡ failure separatorNoProgress [] remaining exact
  emptySeparatorStopsBeforeElement element separator input ignored remaining exact observed rewrite observed = refl
