{-# OPTIONS --safe #-}
-- Lookups have deliberately different predicates: events require a running
-- trace, while finishing selects the first matching identity in any state.
module Mimir.JudgeTraceSelection where

open import Data.Product using (_×_)
open import Data.String using (toList)
open import Relation.Nullary using (Dec; _×-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.JudgeStateRecords as Records
import Mimir.FirstListMatch as First

module Over (Id : Set) (equal : (x y : Id) → Dec (x ≡ y)) where
  module R = Records.Over Id

  Matching : Id → R.Trace → Set
  Matching identity trace = R.Trace.identity trace ≡ identity

  matching? : ∀ identity trace → Dec (Matching identity trace)
  matching? identity trace = equal (R.Trace.identity trace) identity

  Running : Id → R.Trace → Set
  Running identity trace = Matching identity trace × R.Trace.status trace ≡ toList "running"

  running? : ∀ identity trace → Dec (Running identity trace)
  running? identity trace = matching? identity trace ×-dec (R.Trace.status trace ≟Text toList "running")

  module Finishing (identity : Id) = First.Over R.Trace (Matching identity) (matching? identity)
  module Recording (identity : Id) = First.Over R.Trace (Running identity) (running? identity)
