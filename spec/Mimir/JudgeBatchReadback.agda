{-# OPTIONS --safe #-}
-- Final classification rereads every originally selected revision, including
-- ones not attempted after an earlier failure. Intermediate controller results
-- cannot replace these reads or remove an unfinished selection.
module Mimir.JudgeBatchReadback where

open import Data.Bool using (Bool; true; false)
open import Data.Bool.ListAction using (all; any)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Mimir.Text using (Text)
open import Mimir.UUIDGroups using (UUID)
import Mimir.ReviewObservation as O
import Mimir.BatchReport as Batch
import Mimir.JudgeAcknowledgement as Acknowledgement
import Mimir.JudgeStateRecords as Records
import Mimir.Judge as Judge
import Mimir.Effects as Effects
import Mimir.SourceFailure as Source
import Mimir.Validation as Validation

module R = Records.Over UUID

record Failure : Set where
  constructor failure
  field detail : Text; source : Maybe Source.Failure

data Effect : Set where getExperience : O.Pin → Effect; clock : Effect
Reply : Effect → Set
Reply (getExperience chosen) = Failure ⊎ Maybe O.Snapshot
Reply clock = Maybe ℕ
module E = Effects.Protocol Effect Reply
open E

receipt : (chosen : O.Pin) → Reply (getExperience chosen) → O.Receipt chosen
receipt chosen (inj₁ error) = O.unavailable
receipt chosen (inj₂ observed) = O.observe chosen observed

data TranscriptDisposition : Set where
  discard publish verifyBeforePublishing : TranscriptDisposition

transcriptDisposition : Judge.Completion.Receipt → TranscriptDisposition
transcriptDisposition Judge.Completion.confirmed = discard
transcriptDisposition Judge.Completion.corrected = discard
transcriptDisposition Judge.Completion.pending = publish
transcriptDisposition Judge.Completion.unavailable = verifyBeforePublishing

-- This applies to each actual attempt regardless of the other batch receipts.
confirmedTranscriptIsDiscarded : ∀ {chosen} (outcome : O.Receipt chosen) →
  Batch.label outcome ≡ Judge.Completion.confirmed →
  transcriptDisposition (Batch.label outcome) ≡ discard
confirmedTranscriptIsDiscarded outcome confirmed = cong transcriptDisposition confirmed

captureFailure : O.Pin → Failure → R.Report → Script R.Report
captureFailure chosen error before with R.Report.diagnostic before
... | just existing = done (R.captureSource (Failure.source error) before)
... | nothing = ask clock (λ observed → done (record (R.captureSource (Failure.source error) before)
    { diagnostic = just (R.newDiagnostic observed (O.Pin.identity chosen) (toList "get_experience") (Failure.detail error)) }))

readAll : (pins : List O.Pin) → R.Report → Script (Batch.Batch pins × R.Report)
readAll [] before = done (Batch.empty , before)
readAll (chosen ∷ remaining) before = ask (getExperience chosen) (λ reply →
  capture reply >>= λ updated → readAll remaining updated >>= λ { (rest , final) →
    done (Batch.entry (receipt chosen reply) rest , final) })
  where
  capture : Reply (getExperience chosen) → Script R.Report
  capture (inj₁ error) = captureFailure chosen error before
  capture (inj₂ snapshot) with O.observe chosen snapshot
  ... | O.malformed error = captureFailure chosen
      (failure (Validation.Fault.explanation error) nothing) before
  ... | _ = done before

statusText : Judge.Completion.Status → Text
statusText Judge.Completion.idle = toList "idle"
statusText Judge.Completion.running = toList "running"
statusText Judge.Completion.partial = toList "partial"
statusText Judge.Completion.complete = toList "complete"
statusText Judge.Completion.blocked = toList "blocked"

sourceChanged : List Judge.Completion.Receipt → Bool
sourceChanged receipts with all readable receipts
  where
  readable : Judge.Completion.Receipt → Bool
  readable Judge.Completion.confirmed = true
  readable Judge.Completion.corrected = true
  readable _ = false
... | false = false
... | true = any changed receipts
  where
  changed : Judge.Completion.Receipt → Bool
  changed Judge.Completion.corrected = true
  changed _ = false

reason : Bool → Judge.Completion.Status → List Judge.Completion.Receipt → List O.Deferred → Maybe Text → Maybe Text
reason failed Judge.Completion.complete receipts deferred existing = nothing
reason failed status receipts deferred (just existing) = just existing
reason true status receipts deferred nothing = just (toList "incomplete")
reason false Judge.Completion.idle receipts deferred nothing = nothing
reason false status receipts deferred nothing with sourceChanged receipts
... | true = just (toList "review_source_changed")
... | false with deferred
...   | [] = just (toList "revision_not_confirmed")
...   | _ ∷ _ = just (toList "review_deferred")

report : ∀ {pins} → R.Report → Bool → Batch.Batch pins → List O.Deferred → R.Report
report {pins} before failed observations deferred = record before
  { selectedIds = map O.Pin.identity pins
  ; status = statusText status
  ; deferredReviews = map (λ d → R.deferred (O.Deferred.identity d) (O.Deferred.revision d)) deferred
  ; blockReason = reason failed status (Batch.labels observations) deferred (R.Report.blockReason before) }
  where
  summary = Batch.finish observations deferred
  status = Batch.Report.status summary

-- A pin whose final readback stays pending — the stored revision still
-- matches the selection but no review was confirmed — joins the deferred
-- set instead of leaving the batch without deferrals. Deferral excludes the
-- pin from subsequent selections and schedules reconciliation against fresh
-- reads (Mimir.DeferredReviews); it never parks unrelated pending work.
pendingDeferrals : ∀ {pins} → Batch.Batch pins → List O.Deferred
pendingDeferrals Batch.empty = []
pendingDeferrals (Batch.entry {pin = selectedPin} (O.found observed valid (O.pending identity same unconfirmed)) rest) =
  O.deferred (O.Pin.identity selectedPin) (O.Pin.sourceRevision selectedPin) ∷ pendingDeferrals rest
pendingDeferrals (Batch.entry receipt rest) = pendingDeferrals rest

finish : (pins : List O.Pin) → R.Report → Bool → List O.Deferred →
  Script (Σ R.Report (λ result → Maybe (Acknowledgement.BatchEvidence (R.Report.selectedIds result))))
finish pins before failed deferred = readAll pins before >>= λ { (observations , updated) →
  finishObserved observations updated }
  where
  finishObserved : Batch.Batch pins → R.Report →
    Script (Σ R.Report (λ result → Maybe (Acknowledgement.BatchEvidence (R.Report.selectedIds result))))
  finishObserved observations updated with Batch.Report.status
    (Batch.finish observations (deferred ++ pendingDeferrals observations)) in status
  ... | Judge.Completion.complete = done (report updated failed observations
        (deferred ++ pendingDeferrals observations) , just
    (Acknowledgement.batchEvidence pins refl
      (Batch.completeRequiresEvidenceForEverySelection observations
        (deferred ++ pendingDeferrals observations) status)))
  ... | _ = done (report updated failed observations
        (deferred ++ pendingDeferrals observations) , nothing)

selectionRetained : ∀ {pins} before failed (observations : Batch.Batch pins) deferred →
  R.Report.selectedIds (report before failed observations deferred) ≡ map O.Pin.identity pins
selectionRetained before failed observations deferred = refl

-- A completed readback replaces an earlier blocking reason, but it does not
-- erase the retained diagnostic or failure detail that explains the attempt.
confirmedReadbackRetainsEvidence : ∀ {pins} before failed (observations : Batch.Batch pins) deferred →
  Batch.Report.status (Batch.finish observations deferred) ≡ Judge.Completion.complete →
  (R.Report.blockReason (report before failed observations deferred) ≡ nothing) ×
  (R.Report.diagnostic (report before failed observations deferred) ≡ R.Report.diagnostic before) ×
  (R.Report.failureDetail (report before failed observations deferred) ≡ R.Report.failureDetail before)
confirmedReadbackRetainsEvidence before failed observations deferred confirmed rewrite confirmed = refl , refl , refl
