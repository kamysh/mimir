{-# OPTIONS --safe #-}
-- Compose individual review results with batch completion. The batch retains
-- every selected chosen, including failures; filtering pending items before this
-- calculation would not implement this contract.
module Mimir.JudgeBatchConfirmation where

open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
import Mimir.Judge as Judge
import Mimir.JudgeReview as Review
import Mimir.ReviewObservation as Observation
import Mimir.JudgeAcknowledgement as Acknowledgement

module Over (Payload : Set) where
  module Batch = Judge.Completion

  record Entry : Set where
    constructor entry
    field
      selected : Observation.Pin
      result : Review.Controller.Result Payload selected

  classify : ∀ selected → Review.Controller.Result Payload selected → Batch.Receipt
  classify selected (Review.Controller.confirmed proof) = Batch.confirmed
  classify selected Review.Controller.sourceChanged = Batch.corrected
  classify selected Review.Controller.unreviewed = Batch.pending
  classify selected Review.Controller.transportInterrupted = Batch.unavailable
  classify selected Review.Controller.transportFailed = Batch.unavailable
  classify selected Review.Controller.serviceFailed = Batch.unavailable
  classify selected Review.Controller.traceFailed = Batch.unavailable
  classify selected Review.Controller.stopped = Batch.unavailable

  receipt : Entry → Batch.Receipt
  receipt e = classify (Entry.selected e) (Entry.result e)

  Witness : Entry → Set
  Witness e = Σ (Acknowledgement.Evidence (Entry.selected e))
    (λ proof → Entry.result e ≡ Review.Controller.confirmed proof)

  classifySound : ∀ selected result → Batch.Confirmed (classify selected result) →
    Witness (entry selected result)
  classifySound selected (Review.Controller.confirmed proof) accepted = proof , refl
  classifySound selected Review.Controller.sourceChanged ()
  classifySound selected Review.Controller.unreviewed ()
  classifySound selected Review.Controller.transportInterrupted ()
  classifySound selected Review.Controller.transportFailed ()
  classifySound selected Review.Controller.serviceFailed ()
  classifySound selected Review.Controller.traceFailed ()
  classifySound selected Review.Controller.stopped ()

  allWitnesses : ∀ entries → All Batch.Confirmed (map receipt entries) → All Witness entries
  allWitnesses [] [] = []
  allWitnesses (entry selected result ∷ entries) (accepted ∷ rest) = classifySound selected result accepted ∷ allWitnesses entries rest

  finish : List Entry → Bool → Batch.Status
  finish entries failed = Batch.finish (map receipt entries) failed

  completeRequiresEverySelectedReceipt : ∀ entries failed →
    finish entries failed ≡ Batch.complete → All Witness entries
  completeRequiresEverySelectedReceipt entries failed completed = allWitnesses entries
    (Batch.complete-requires-database-receipts (map receipt entries)
     failed completed)

  -- Index results by the ORIGINAL selection, so a caller cannot satisfy the
  -- completion contract by discarding unfinished entries from its report.
  Results : List Observation.Pin → Set
  Results selected = All (Review.Controller.Result Payload) selected

  collect : (selected : List Observation.Pin) → Results selected → List Entry
  collect [] [] = []
  collect (chosen ∷ selected) (result ∷ results) = entry chosen result ∷ collect selected results

  preservesSelection : ∀ selected results →
    map Entry.selected (collect selected results) ≡ selected
  preservesSelection [] [] = refl
  preservesSelection (chosen ∷ selected) (result ∷ results) = cong (chosen ∷_) (preservesSelection selected results)

  collectEvidence : ∀ selected results → All Witness (collect selected results) →
    All Acknowledgement.Evidence selected
  collectEvidence [] [] [] = []
  collectEvidence (chosen ∷ selected) (result ∷ results) ((proof , same) ∷ witnesses) = proof ∷ collectEvidence selected results witnesses

  completeSelectionHasEvidence : ∀ selected (results : Results selected) failed →
    finish (collect selected results) failed ≡ Batch.complete →
    All Acknowledgement.Evidence selected
  completeSelectionHasEvidence selected results failed completed = collectEvidence selected results
    (completeRequiresEverySelectedReceipt (collect selected results)
     failed completed)
