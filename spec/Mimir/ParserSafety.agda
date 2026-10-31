{-# OPTIONS --safe #-}
-- Compositional exclusion of partial-stream and no-progress failures.
-- These are properties of parser results, not assumptions about their callers.
module Mimir.ParserSafety where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++-≤ʳ)
open import Data.Nat using (zero; suc; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.BacktrackingParser as Backtracking

module Laws (Atom Error Needed : Set) (merge : Error → Error → Error)
  (appendAlternative : Error → Error) where
  module P = Backtracking.Parsers Atom Error Needed merge appendAlternative
  open P

  data Ordinary : Failure → Set where
    recoverable : ∀ error → Ordinary (backtrack error)
    fatal : ∀ error → Ordinary (cut error)

  Clean : ∀ {A input} → Result A input → Set
  Clean (success value consumed remaining exact) = ⊤
  Clean (failure code consumed remaining exact) = Ordinary code

  Advances : ∀ {A input} → Result A input → Set
  Advances (success value consumed remaining exact) = 1 ≤ length consumed
  Advances (failure code consumed remaining exact) = ⊤

  CleanParser : ∀ {A} → Parser A → Set
  CleanParser parser = ∀ input → Clean (parser input)

  AdvancingParser : ∀ {A} → Parser A → Set
  AdvancingParser parser = ∀ input → Advances (parser input)

  cleanMap : ∀ {A B input} (f : A → B) (result : Result A input) →
    Clean result → Clean (mapResult f result)
  cleanMap f (success value before after exact) proof = tt
  cleanMap f (failure code before after exact) proof = proof

  advancesMap : ∀ {A B input} (f : A → B) (result : Result A input) →
    Advances result → Advances (mapResult f result)
  advancesMap f (success value before after exact) proof = proof
  advancesMap f (failure code before after exact) proof = tt

  cleanPrefix : ∀ {A input} before (result : Result A input) →
    Clean result → Clean (prefix before result)
  cleanPrefix before (success value consumed remaining exact) proof = tt
  cleanPrefix before (failure code consumed remaining exact) proof = proof

  advancesPrefix : ∀ {A input} before (result : Result A input) →
    Advances result → Advances (prefix before result)
  advancesPrefix before (success value consumed remaining exact) proof =
    ≤-trans proof (length-++-≤ʳ consumed {xs = before})
  advancesPrefix before (failure code consumed remaining exact) proof = tt

  positivePrefix : ∀ {A input} char before (result : Result A input) →
    Advances (prefix (char ∷ before) result)
  positivePrefix char before (success value consumed remaining exact) = s≤s z≤n
  positivePrefix char before (failure code consumed remaining exact) = tt

  cleanReframe : ∀ {A input source} (same : input ≡ source) (result : Result A source) →
    Clean result → Clean (reframe same result)
  cleanReframe refl result proof = proof

  advancesReframe : ∀ {A input source} (same : input ≡ source) (result : Result A source) →
    Advances result → Advances (reframe same result)
  advancesReframe refl result proof = proof

  cleanBind : ∀ {A B input} (result : Result A input) (next : A → Parser B) →
    Clean result → (∀ value → CleanParser (next value)) → Clean (andThen result next)
  cleanBind (failure code before after exact) next proof nextClean = proof
  cleanBind (success value before after exact) next proof nextClean =
    cleanReframe exact _ (cleanPrefix before _ (nextClean value after))

  advancesBindFirst : ∀ {A B input} (result : Result A input) (next : A → Parser B) →
    Advances result → Advances (andThen result next)
  advancesBindFirst (failure code before after exact) next proof = tt
  advancesBindFirst (success value [] after exact) next ()
  advancesBindFirst (success value (char ∷ before) after exact) next proof =
    advancesReframe exact _ (positivePrefix char before (next value after))

  advancesBindNext : ∀ {A B input} (result : Result A input) (next : A → Parser B) →
    (∀ value → AdvancingParser (next value)) → Advances (andThen result next)
  advancesBindNext (failure code before after exact) next nextProgress = tt
  advancesBindNext (success value before after exact) next nextProgress =
    advancesReframe exact _ (advancesPrefix before _ (nextProgress value after))

  cleanAlternativeResult : ∀ {A input} error (result : Result A input) →
    Clean result → Clean (alternativeResult error result)
  cleanAlternativeResult error (success value before after exact) proof = tt
  cleanAlternativeResult error (failure (backtrack other) before after exact) proof = recoverable _
  cleanAlternativeResult error (failure (cut other) before after exact) proof = proof
  cleanAlternativeResult error (failure (incomplete needed) before after exact) ()
  cleanAlternativeResult error (failure repeatNoProgress before after exact) ()
  cleanAlternativeResult error (failure separatorNoProgress before after exact) ()

  advancesAlternativeResult : ∀ {A input} error (result : Result A input) →
    Advances result → Advances (alternativeResult error result)
  advancesAlternativeResult error (success value before after exact) proof = proof
  advancesAlternativeResult error (failure (backtrack other) before after exact) proof = tt
  advancesAlternativeResult error (failure (cut other) before after exact) proof = tt
  advancesAlternativeResult error (failure (incomplete needed) before after exact) proof = tt
  advancesAlternativeResult error (failure repeatNoProgress before after exact) proof = tt
  advancesAlternativeResult error (failure separatorNoProgress before after exact) proof = tt

  cleanAlternative : ∀ {A} (first second : Parser A) →
    CleanParser first → CleanParser second → CleanParser (alternative first second)
  cleanAlternative first second firstClean secondClean input with first input | firstClean input
  ... | success value before after exact | proof = tt
  ... | failure (backtrack error) before after exact | proof = cleanAlternativeResult error _ (secondClean input)
  ... | failure (cut error) before after exact | proof = proof
  ... | failure (incomplete needed) before after exact | ()
  ... | failure repeatNoProgress before after exact | ()
  ... | failure separatorNoProgress before after exact | ()

  advancesAlternative : ∀ {A} (first second : Parser A) →
    AdvancingParser first → AdvancingParser second → AdvancingParser (alternative first second)
  advancesAlternative first second firstProgress secondProgress input with first input | firstProgress input
  ... | success value before after exact | proof = proof
  ... | failure (backtrack error) before after exact | proof = advancesAlternativeResult error _ (secondProgress input)
  ... | failure (cut error) before after exact | proof = tt
  ... | failure (incomplete needed) before after exact | proof = tt
  ... | failure repeatNoProgress before after exact | proof = tt
  ... | failure separatorNoProgress before after exact | proof = tt

  cleanRepeatBounded : ∀ {A} (parser : Parser A) → CleanParser parser → AdvancingParser parser →
    ∀ fuel input bounded → Clean (repeatBounded parser fuel input bounded)
  cleanRepeatBounded parser parserClean parserProgress zero input ()
  cleanRepeatBounded parser parserClean parserProgress (suc fuel) input bounded
    with parser input | parserClean input | parserProgress input
  ... | failure (backtrack error) before after exact | clean | progress = tt
  ... | failure (cut error) before after exact | clean | progress = clean
  ... | failure (incomplete needed) before after exact | () | progress
  ... | failure repeatNoProgress before after exact | () | progress
  ... | failure separatorNoProgress before after exact | () | progress
  ... | success value [] after exact | clean | ()
  ... | success value (char ∷ before) after exact | clean | progress =
    cleanReframe exact _ (cleanPrefix (char ∷ before) _ (cleanMap (value ∷_) _
      (cleanRepeatBounded parser parserClean parserProgress fuel after
        (strictSuffix fuel input char before after exact bounded))))

  cleanRepeat : ∀ {A} (parser : Parser A) → CleanParser parser → AdvancingParser parser →
    CleanParser (repeat parser)
  cleanRepeat parser parserClean parserProgress input =
    cleanRepeatBounded parser parserClean parserProgress (suc (length input)) input (s≤s ≤-refl)

  cleanSeparatorThen : ∀ {A B} (element : Parser A) (separator : Parser B) →
    CleanParser element → CleanParser separator → AdvancingParser separator →
    CleanParser (separatorThen element separator)
  cleanSeparatorThen element separator elementClean separatorClean separatorProgress input
    with separator input | separatorClean input | separatorProgress input
  ... | failure code before after exact | clean | progress = clean
  ... | success ignored [] after exact | clean | ()
  ... | success ignored (char ∷ before) after exact | clean | progress =
    cleanReframe exact _ (cleanPrefix (char ∷ before) _ (elementClean after))

  advancesSeparatorThen : ∀ {A B} (element : Parser A) (separator : Parser B) →
    AdvancingParser (separatorThen element separator)
  advancesSeparatorThen element separator input with separator input
  ... | failure code before after exact = tt
  ... | success ignored [] after exact = tt
  ... | success ignored (char ∷ before) after exact =
    advancesReframe exact _ (positivePrefix char before (element after))

  cleanSeparated : ∀ {A B} (element : Parser A) (separator : Parser B) →
    CleanParser element → CleanParser separator → AdvancingParser separator →
    CleanParser (separated element separator)
  cleanSeparated element separator elementClean separatorClean separatorProgress input
    with element input | elementClean input
  ... | failure (backtrack error) before after exact | clean = tt
  ... | failure (cut error) before after exact | clean = clean
  ... | failure (incomplete needed) before after exact | ()
  ... | failure repeatNoProgress before after exact | ()
  ... | failure separatorNoProgress before after exact | ()
  ... | success value before after exact | clean =
    cleanReframe exact _ (cleanPrefix before _ (cleanMap (value ∷_) _
      (cleanRepeat (separatorThen element separator)
        (cleanSeparatorThen element separator elementClean separatorClean separatorProgress)
        (advancesSeparatorThen element separator) after)))
