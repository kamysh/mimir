{-# OPTIONS --safe #-}
-- Classify the existing revision-checking function before journal effects are
-- chosen. A replay and a fresh review must not share an append-history branch.
module Mimir.ReviewPlan where

open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; _≟_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.LearningContracts as Contracts

module Over (Payload : Set) (equal : DecidableEquality Payload) where
  module R = Contracts.Revision Payload equal

  data Plan (before : R.Cell) (payload : Payload) : Maybe R.Cell → Set where
    refused : Plan before payload nothing
    replayed : Plan before payload (just before)
    fresh : Plan before payload (just (R.commit before payload))

  classify : ∀ before owner source expected payload valid →
    Plan before payload (R.submit before owner source expected payload valid)
  classify before owner source expected payload valid
    with owner ≟Text R.Cell.project before | source ≟ R.Cell.current before
  ... | no _ | _ = refused
  ... | yes _ | no _ = refused
  ... | yes _ | yes _ with R.replay before expected payload
  ...   | true = replayed
  ...   | false with expected ≟ R.Cell.review before | valid
  ...     | no _ | _ = refused
  ...     | yes _ | false = refused
  ...     | yes _ | true = fresh

  -- The plan type itself prevents a confirmed exact replay from being
  -- reclassified as a new journal entry with a higher review revision.
  data IsReplay {before payload} : ∀ {after} → Plan before payload after → Set where
    isReplay : IsReplay replayed

  unchangedMeansReplay : ∀ before payload {after} (plan : Plan before payload after) →
    after ≡ just before → IsReplay plan
  unchangedMeansReplay before payload refused ()
  unchangedMeansReplay before payload replayed same = isReplay
  unchangedMeansReplay before payload fresh same = ⊥-elim
    (Contracts.not-successor (R.Cell.review before)
     (sym (cong R.Cell.review (just-injective same))))
