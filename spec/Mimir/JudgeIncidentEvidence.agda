{-# OPTIONS --safe #-}
-- Every newly recorded confirmation is justified by the completed-batch
-- branch and both identity selections. Idle/failure transitions cannot add one.
module Mimir.JudgeIncidentEvidence where

open import Data.List using (List; [])
open import Data.List.Relation.Unary.Any using (Any)
import Data.List.Relation.Unary.Any.Properties as Any
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.String using (toList)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
import Mimir.JudgeStateRecords as Records
import Mimir.JudgeIncident as Incident
import Mimir.JudgeConfirmationLedger as Ledger

module Over (Id : Set) (equal : (x y : Id) → Dec (x ≡ y)) where
  module R = Records.Over Id
  module I = Incident.Over Id equal
  module L = Ledger.Over Id equal

  previous : Maybe R.Incident → List R.Confirmed
  previous nothing = []
  previous (just value) = R.Incident.confirmedReviews value

  newlyAdded : ∀ {report before after} → I.Transition report before (just after) →
    ∀ entry → Any (entry ≡_) (R.Incident.confirmedReviews after) → ¬ Any (entry ≡_) (previous before) →
    Σ R.Incident (λ original → before ≡ just original ×
      (R.Report.status report ≡ toList "complete" × (I.CompleteCounts report ×
      L.Eligible (R.Report.selectedIds (R.Incident.first original)) (R.Report.selectedIds report) (R.Report.recordedAt report) entry)))
  newlyAdded (I.firstFailure failed) entry () absent
  newlyAdded (I.nextFailure before at failed recovered) entry () absent
  newlyAdded (I.latestFailure before failed openIncident) entry present absent = ⊥-elim (absent present)
  newlyAdded (I.idleRecovery before idle openIncident) entry present absent = ⊥-elim (absent present)
  newlyAdded (I.batchConfirmation before after first additions complete counts openIncident updates) entry present absent
    with Any.++⁻ (R.Incident.confirmedReviews before)
      (subst (Any (entry ≡_)) (L.appendedExactly updates) present)
  ... | inj₁ old = ⊥-elim (absent old)
  ... | inj₂ added = before , refl , complete , counts , All.lookup (L.onlyEligibleAdded updates) added
