{-# OPTIONS --safe #-}
module Mimir.UnicodeParserSafety where

open import Data.List using ([]; _∷_; length)
open import Data.Nat using (zero; suc; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Unit using (tt)
open import Mimir.UnicodeParser
open Raw using (Result; success; failure; backtrack; cut; incomplete;
  repeatNoProgress; separatorNoProgress)
import Mimir.MigrationParserSafety as Safety
open Safety.L using (Clean; Advances; recoverable; fatal; cleanReframe; cleanPrefix;
  cleanMap; advancesReframe; positivePrefix)

CleanParser : ∀ {A} → Parser A → Set
CleanParser parser = ∀ input valid → Clean (parser input valid)

AdvancingParser : ∀ {A} → Parser A → Set
AdvancingParser parser = ∀ input valid → Advances (parser input valid)

cleanLift : ∀ {A} (parser : Raw.Parser A) → Safety.L.CleanParser parser → CleanParser (lift parser)
cleanLift parser proof input valid = proof input

advancesLift : ∀ {A} (parser : Raw.Parser A) → Safety.L.AdvancingParser parser → AdvancingParser (lift parser)
advancesLift parser proof input valid = proof input

cleanBindResult : ∀ {A B input} (result : Result A input) valid (next : A → Parser B) →
  Clean result → (∀ value → CleanParser (next value)) → Clean (bindResult result valid next)
cleanBindResult (failure code before after exact) valid next proof nextClean = proof
cleanBindResult result@(success value before after exact) valid next proof nextClean =
  cleanReframe exact _ (cleanPrefix before _ (nextClean value after (remainingValid result valid)))

cleanBind : ∀ {A B} (first : Parser A) (next : A → Parser B) →
  CleanParser first → (∀ value → CleanParser (next value)) → CleanParser (bind first next)
cleanBind first next firstClean nextClean input valid = cleanBindResult (first input valid) valid next (firstClean input valid) nextClean

advancesBindResult : ∀ {A B input} (result : Result A input) valid (next : A → Parser B) →
  Advances result → Advances (bindResult result valid next)
advancesBindResult (failure code before after exact) valid next proof = tt
advancesBindResult (success value [] after exact) valid next ()
advancesBindResult result@(success value (char ∷ before) after exact) valid next proof =
  advancesReframe exact _ (positivePrefix char before (next value after (remainingValid result valid)))

advancesBind : ∀ {A B} (first : Parser A) (next : A → Parser B) →
  AdvancingParser first → AdvancingParser (bind first next)
advancesBind first next proof input valid = advancesBindResult (first input valid) valid next (proof input valid)

cleanRepeatBounded : ∀ {A} (parser : Parser A) → CleanParser parser → AdvancingParser parser →
  ∀ fuel input valid bounded → Clean (Mimir.UnicodeParser.repeatBounded parser fuel input valid bounded)
cleanRepeatBounded parser parserClean parserProgress zero input valid ()
cleanRepeatBounded parser parserClean parserProgress (suc fuel) input valid bounded
  with parser input valid | parserClean input valid | parserProgress input valid
... | failure (backtrack error) before after exact | clean | progress = tt
... | failure (cut error) before after exact | clean | progress = clean
... | failure (incomplete needed) before after exact | () | progress
... | failure repeatNoProgress before after exact | () | progress
... | failure separatorNoProgress before after exact | () | progress
... | success value [] after exact | clean | ()
... | result@(success value (char ∷ before) after exact) | clean | progress =
  cleanReframe exact _ (cleanPrefix (char ∷ before) _ (cleanMap (value ∷_) _
    (cleanRepeatBounded parser parserClean parserProgress fuel after
      (remainingValid result valid) (Raw.strictSuffix fuel input char before after exact bounded))))

cleanRepeat : ∀ {A} (parser : Parser A) → CleanParser parser → AdvancingParser parser →
  CleanParser (Mimir.UnicodeParser.repeat parser)
cleanRepeat parser parserClean parserProgress input valid =
  cleanRepeatBounded parser parserClean parserProgress (suc (length input)) input valid (s≤s ≤-refl)
