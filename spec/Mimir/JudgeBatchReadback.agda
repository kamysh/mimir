{-# OPTIONS --safe #-}
-- Final classification rereads every originally selected revision, including
-- ones not attempted after an earlier failure. Intermediate controller results
-- cannot replace these reads or remove an unfinished selection.
module Mimir.JudgeBatchReadback where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.ReviewObservation as O
import Mimir.BatchReport as Batch
import Mimir.JudgeStateRecords as Records
import Mimir.Judge as Judge
import Mimir.Effects as Effects
import Mimir.SourceFailure as Source
import Mimir.Validation as Validation

module R = Records.Over ℕ

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

reason : Bool → Judge.Completion.Status → List O.Deferred → Maybe Text → Maybe Text
reason failed status deferred (just existing) = just existing
reason true status deferred nothing = just (toList "incomplete")
reason false Judge.Completion.complete deferred nothing = nothing
reason false Judge.Completion.idle deferred nothing = nothing
reason false status [] nothing = just (toList "revision_not_confirmed")
reason false status (_ ∷ _) nothing = just (toList "review_deferred")

report : ∀ {pins} → R.Report → Bool → Batch.Batch pins → List O.Deferred → R.Report
report {pins} before failed observations deferred = record before
  { selected = length pins
  ; selectedIds = map O.Pin.identity pins
  ; confirmed = Batch.Counts.confirmed counts
  ; corrected = Batch.Counts.corrected counts
  ; pending = Batch.Counts.pending counts
  ; unavailable = Batch.Counts.unavailable counts
  ; status = statusText status
  ; deferredReviews = map (λ d → R.deferred (O.Deferred.identity d) (O.Deferred.revision d)) deferred
  ; blockReason = reason failed status deferred (R.Report.blockReason before) }
  where
  summary = Batch.finish observations deferred
  counts = Batch.Report.outcomes summary
  status = Batch.Report.status summary

finish : (pins : List O.Pin) → R.Report → Bool → List O.Deferred → Script R.Report
finish pins before failed deferred = readAll pins before >>= λ { (observations , updated) →
  done (report updated failed observations deferred) }

selectionRetained : ∀ {pins} before failed (observations : Batch.Batch pins) deferred →
  R.Report.selectedIds (report before failed observations deferred) ≡ map O.Pin.identity pins
selectionRetained before failed observations deferred = refl
