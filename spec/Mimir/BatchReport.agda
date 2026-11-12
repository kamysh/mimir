{-# OPTIONS --safe #-}
-- Every selected revision gets a final database observation. Completion is
-- determined by those observations, independently of reported statistics.
module Mimir.BatchReport where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
import Mimir.Judge as Judge
import Mimir.ReviewObservation as Observation
open import Mimir.JudgeAcknowledgement using (Evidence; evidence)

module Summary = Judge.Completion

data Batch : List Observation.Pin → Set where
  empty : Batch []
  entry : ∀ {pin rest} → Observation.Receipt pin → Batch rest → Batch (pin ∷ rest)

label : ∀ {pin} → Observation.Receipt pin → Summary.Receipt
label Observation.unavailable = Summary.unavailable
label (Observation.malformed failure) = Summary.unavailable
label (Observation.found observed valid (Observation.confirmed acknowledgement)) = Summary.confirmed
label (Observation.found observed valid (Observation.corrected identity changed)) = Summary.corrected
label (Observation.found observed valid (Observation.pending identity same unconfirmed)) = Summary.pending

labels : ∀ {pins} → Batch pins → List Summary.Receipt
labels empty = []
labels (entry receipt rest) = label receipt ∷ labels rest

hasDeferred : List Observation.Deferred → Bool
hasDeferred [] = false
hasDeferred (_ ∷ _) = true

record Report : Set where
  constructor report
  field status : Summary.Status

finish : ∀ {pins} → Batch pins → List Observation.Deferred → Report
finish batch deferred = report (Summary.finish (labels batch) (hasDeferred deferred))

confirmedEvidence : ∀ {pin} (receipt : Observation.Receipt pin) →
  Summary.Confirmed (label receipt) → Evidence pin
confirmedEvidence Observation.unavailable impossible = ⊥-elim impossible
confirmedEvidence (Observation.malformed failure) impossible = ⊥-elim impossible
confirmedEvidence (Observation.found observed valid (Observation.confirmed acknowledgement)) proof = evidence observed valid acknowledgement
confirmedEvidence (Observation.found observed valid (Observation.corrected identity changed)) impossible = ⊥-elim impossible
confirmedEvidence (Observation.found observed valid (Observation.pending identity same unconfirmed)) impossible = ⊥-elim impossible

allEvidence : ∀ {pins} (batch : Batch pins) → All Summary.Confirmed (labels batch) → All Evidence pins
allEvidence empty [] = []
allEvidence (entry receipt rest) (confirmed ∷ confirmations) =
  confirmedEvidence receipt confirmed ∷ allEvidence rest confirmations

completeRequiresEvidenceForEverySelection : ∀ {pins} (batch : Batch pins) deferred →
  Report.status (finish batch deferred) ≡ Summary.complete → All Evidence pins
completeRequiresEvidenceForEverySelection batch deferred complete = allEvidence batch
  (Summary.complete-requires-database-receipts (labels batch) (hasDeferred deferred) complete)

heldCannotComplete : ∀ receipts → Summary.finish receipts true ≢ Summary.complete
heldCannotComplete [] ()
heldCannotComplete (receipt ∷ rest) impossible with Summary.anyConfirmed (receipt ∷ rest)
... | true with impossible
...   | ()
heldCannotComplete (receipt ∷ rest) impossible | false with impossible
... | ()

completeHasNoDeferred : ∀ {pins} (batch : Batch pins) deferred →
  Report.status (finish batch deferred) ≡ Summary.complete → deferred ≡ []
completeHasNoDeferred batch [] proof = refl
completeHasNoDeferred batch (held ∷ rest) proof = ⊥-elim (heldCannotComplete (labels batch) proof)

allConfirmedTrue : ∀ receipts → All Summary.Confirmed receipts → Summary.allConfirmed receipts ≡ true
allConfirmedTrue [] [] = refl
allConfirmedTrue (Summary.confirmed ∷ rest) (proof ∷ proofs) = allConfirmedTrue rest proofs
allConfirmedTrue (Summary.pending ∷ rest) (() ∷ proofs)
allConfirmedTrue (Summary.corrected ∷ rest) (() ∷ proofs)
allConfirmedTrue (Summary.unavailable ∷ rest) (() ∷ proofs)

confirmedNonemptyCompletes : ∀ {pin pins} (receipt : Observation.Receipt pin) (rest : Batch pins) →
  All Summary.Confirmed (labels (entry receipt rest)) →
  Report.status (finish (entry receipt rest) []) ≡ Summary.complete
confirmedNonemptyCompletes receipt rest confirmed
  rewrite allConfirmedTrue (labels (entry receipt rest)) confirmed = refl
