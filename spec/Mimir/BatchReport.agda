{-# OPTIONS --safe #-}
-- Every selected revision gets exactly one final database observation. Counts
-- and status are derived together, rather than supplied independently.
module Mimir.BatchReport where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc)
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans)
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

oneObservationPerSelection : ∀ {pins} (batch : Batch pins) → length (labels batch) ≡ length pins
oneObservationPerSelection empty = refl
oneObservationPerSelection (entry receipt rest) = cong suc (oneObservationPerSelection rest)

record Counts : Set where
  constructor counts
  field confirmed corrected pending unavailable : ℕ

increment : Summary.Receipt → Counts → Counts
increment Summary.confirmed (counts c r p u) = counts (suc c) r p u
increment Summary.corrected (counts c r p u) = counts c (suc r) p u
increment Summary.pending (counts c r p u) = counts c r (suc p) u
increment Summary.unavailable (counts c r p u) = counts c r p (suc u)

total : Counts → ℕ
total (counts c r p u) = c + (r + (p + u))

incrementAddsOne : ∀ receipt before → total (increment receipt before) ≡ suc (total before)
incrementAddsOne Summary.confirmed (counts c r p u) = refl
incrementAddsOne Summary.corrected (counts c r p u) = +-suc c (r + (p + u))
incrementAddsOne Summary.pending (counts c r p u)
  rewrite +-suc r (p + u) | +-suc c (r + (p + u)) = refl
incrementAddsOne Summary.unavailable (counts c r p u)
  rewrite +-suc p u | +-suc r (p + u) | +-suc c (r + (p + u)) = refl

tally : List Summary.Receipt → Counts
tally [] = counts 0 0 0 0
tally (receipt ∷ rest) = increment receipt (tally rest)

countedExactlyOnce : ∀ receipts → total (tally receipts) ≡ length receipts
countedExactlyOnce [] = refl
countedExactlyOnce (receipt ∷ rest) = trans (incrementAddsOne receipt (tally rest))
  (cong suc (countedExactlyOnce rest))

hasDeferred : List Observation.Deferred → Bool
hasDeferred [] = false
hasDeferred (_ ∷ _) = true

record Report : Set where
  constructor report
  field selected : ℕ; outcomes : Counts; status : Summary.Status

finish : ∀ {pins} → Batch pins → List Observation.Deferred → Report
finish {pins} batch deferred = report (length pins) (tally (labels batch))
  (Summary.finish (labels batch) (hasDeferred deferred))

reportCountsMatchSelection : ∀ {pins} (batch : Batch pins) deferred →
  total (Report.outcomes (finish batch deferred)) ≡ Report.selected (finish batch deferred)
reportCountsMatchSelection batch deferred = trans (countedExactlyOnce (labels batch))
  (oneObservationPerSelection batch)

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
