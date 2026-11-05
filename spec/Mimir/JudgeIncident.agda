{-# OPTIONS --safe #-}
-- Exact incident-write decisions. Idle closes the incident marker without
-- fabricating review confirmations; completed batches use the separate ledger.
module Mimir.JudgeIncident where

open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (toList)
open import Relation.Nullary using (Dec; yes; no; _×-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.JudgeStateRecords as Records
import Mimir.JudgeConfirmationLedger as Ledger

module Over (Id : Set) (equal : (x y : Id) → Dec (x ≡ y)) where
  module R = Records.Over Id
  module L = Ledger.Over Id equal

  Failed : R.Report → Set
  Failed report = R.Report.status report ≡ toList "blocked" ⊎ R.Report.status report ≡ toList "partial"

  CompleteCounts : R.Report → Set
  CompleteCounts report = R.Report.selected report ≡ length (R.Report.selectedIds report) ×
    (R.Report.confirmed report ≡ R.Report.selected report × (R.Report.corrected report ≡ 0 ×
    (R.Report.pending report ≡ 0 × R.Report.unavailable report ≡ 0)))

  counts? : ∀ report → Dec (CompleteCounts report)
  counts? report = (R.Report.selected report ≟ length (R.Report.selectedIds report)) ×-dec
    ((R.Report.confirmed report ≟ R.Report.selected report) ×-dec ((R.Report.corrected report ≟ 0) ×-dec
    ((R.Report.pending report ≟ 0) ×-dec (R.Report.unavailable report ≟ 0))))

  fresh : R.Report → R.Incident
  fresh report = R.incident (R.clearNotification report) nothing [] nothing

  latest : R.Report → R.Incident → R.Incident
  latest report before = record before { latest = just (R.clearNotification report) }

  recovered : R.Report → R.Incident → R.Incident
  recovered report before = record before { recoveredAt = just (R.Report.recordedAt report) }

  confirmations : List R.Confirmed → R.Incident → R.Incident
  confirmations after before = record before { confirmedReviews = after }

  data Transition (report : R.Report) : Maybe R.Incident → Maybe R.Incident → Set where
    unchanged : ∀ before → Transition report before nothing
    firstFailure : Failed report → Transition report nothing (just (fresh report))
    nextFailure : ∀ before at → Failed report → R.Incident.recoveredAt before ≡ just at →
      Transition report (just before) (just (fresh report))
    latestFailure : ∀ before → Failed report → R.Incident.recoveredAt before ≡ nothing →
      Transition report (just before) (just (latest report before))
    idleRecovery : ∀ before → R.Report.status report ≡ toList "idle" → R.Incident.recoveredAt before ≡ nothing →
      Transition report (just before) (just (recovered report before))
    batchConfirmation : ∀ before after first additions → R.Report.status report ≡ toList "complete" →
      CompleteCounts report → R.Incident.recoveredAt before ≡ nothing →
      L.Updates (R.Report.selectedIds (R.Incident.first before)) (R.Report.recordedAt report)
        (R.Report.selectedIds report) (R.Incident.confirmedReviews before) after (first ∷ additions) →
      Transition report (just before) (just (confirmations after before))

  Result : R.Report → Maybe R.Incident → Set
  Result report before = Σ (Maybe R.Incident) (Transition report before)

  failure : ∀ report before → Failed report → Result report before
  failure report nothing failed = just (fresh report) , firstFailure failed
  failure report (just before) failed with R.Incident.recoveredAt before in observed
  ... | nothing = just (latest report before) , latestFailure before failed observed
  ... | just at = just (fresh report) , nextFailure before at failed observed

  idle : ∀ report before → R.Report.status report ≡ toList "idle" → Result report before
  idle report nothing status = nothing , unchanged nothing
  idle report (just before) status with R.Incident.recoveredAt before in observed
  ... | nothing = just (recovered report before) , idleRecovery before status observed
  ... | just at = nothing , unchanged (just before)

  complete : ∀ report before → R.Report.status report ≡ toList "complete" → Result report before
  complete report nothing status = nothing , unchanged nothing
  complete report (just before) status with R.Incident.recoveredAt before in observed
  ... | just at = nothing , unchanged (just before)
  ... | nothing with counts? report
  ...   | no invalid = nothing , unchanged (just before)
  ...   | yes counts with L.collect (R.Report.selectedIds (R.Incident.first before)) (R.Report.recordedAt report)
      (R.Report.selectedIds report) (R.Incident.confirmedReviews before)
  ...     | L.result after [] updates = nothing , unchanged (just before)
  ...     | L.result after (first ∷ additions) updates = just (confirmations after before) ,
    batchConfirmation before after first additions status counts observed updates

  decide : ∀ report before → Result report before
  decide report before with R.Report.status report ≟Text toList "blocked"
  ... | yes blocked = failure report before (inj₁ blocked)
  ... | no notBlocked with R.Report.status report ≟Text toList "partial"
  ...   | yes partial = failure report before (inj₂ partial)
  ...   | no notPartial with R.Report.status report ≟Text toList "idle"
  ...     | yes idleStatus = idle report before idleStatus
  ...     | no notIdle with R.Report.status report ≟Text toList "complete"
  ...       | yes completeStatus = complete report before completeStatus
  ...       | no other = nothing , unchanged before

  idleDoesNotConfirm : ∀ report before →
    R.Incident.confirmedReviews (recovered report before) ≡ R.Incident.confirmedReviews before
  idleDoesNotConfirm report before = refl

  latestRetainsFirst : ∀ report before → R.Incident.first (latest report before) ≡ R.Incident.first before
  latestRetainsFirst report before = refl

  latestRetainsConfirmations : ∀ report before →
    R.Incident.confirmedReviews (latest report before) ≡ R.Incident.confirmedReviews before
  latestRetainsConfirmations report before = refl

  confirmationsDoNotClose : ∀ after before →
    R.Incident.recoveredAt (confirmations after before) ≡ R.Incident.recoveredAt before
  confirmationsDoNotClose after before = refl
