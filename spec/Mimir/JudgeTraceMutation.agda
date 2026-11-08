{-# OPTIONS --safe #-}
-- Complete diagnostic updates. Events and previous evidence remain intact;
-- an operation reports completion only after its private-file write is acknowledged.
module Mimir.JudgeTraceMutation where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.String using (toList)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.Effects as Effects
import Mimir.JudgeStateRecords as Records
import Mimir.JudgeTraceSelection as Selection

module Over (Id : Set) (equal : (x y : Id) → Dec (x ≡ y)) where
  module R = Records.Over Id
  module S = Selection.Over Id equal

  data Operation : Set where
    readDiagnostics clock : Operation
    writeDiagnostics : List R.Trace → Operation

  Reply : Operation → Set
  Reply readDiagnostics = Text ⊎ List R.Trace
  Reply clock = Maybe ℕ
  Reply (writeDiagnostics values) = Text ⊎ ⊤

  open Effects.Protocol Operation Reply public
  data Result : Set where completed : Result; failed : Text → Result

  commit : List R.Trace → Script Result
  commit values = ask (writeDiagnostics values) λ where
    (inj₁ problem) → done (failed problem)
    (inj₂ tt) → done completed

  append : R.Event → R.Trace → R.Trace
  append event before = record before
    { modelRequests = R.Event.modelRequests event
    ; toolAttempts = R.Event.toolAttempts event
    ; events = R.Trace.events before ++ (event ∷ []) }

  appendKeepsEvidence : ∀ event before →
    R.Trace.events (append event before) ≡ R.Trace.events before ++ (event ∷ []) ×
    R.Trace.selectedIds (append event before) ≡ R.Trace.selectedIds before ×
    R.Trace.eventsOmitted (append event before) ≡ R.Trace.eventsOmitted before
  appendKeepsEvidence event before = refl , refl , refl

  foundEvent : Id → R.Event → List R.Trace → Script Result
  foundEvent identity event before with S.Recording.find identity before
  ... | S.Recording.missing absent = done (failed (toList "active diagnostic trace is missing"))
  ... | S.Recording.found selected = commit
    (S.Recording.replace identity selected (append event (S.Recording.Focus.value selected)))

  recordEvent : Id → R.Event → Script Result
  recordEvent identity event = ask readDiagnostics λ where
    (inj₁ problem) → done (failed problem)
    (inj₂ before) → foundEvent identity event before

  finishMetadata : Maybe ℕ → R.Report → R.Trace → R.Trace
  finishMetadata observed report before = record before
    { status = R.Report.status report
    ; blockReason = R.Report.blockReason report
    ; finishedAt = just (Records.clock observed) }

  finishKeepsEvidence : ∀ observed report before →
    R.Trace.events (finishMetadata observed report before) ≡ R.Trace.events before ×
    R.Trace.selectedIds (finishMetadata observed report before) ≡ R.Trace.selectedIds before ×
    R.Trace.eventsOmitted (finishMetadata observed report before) ≡ R.Trace.eventsOmitted before
  finishKeepsEvidence observed report before = refl , refl , refl

  finishSelected : ∀ identity {before} → S.Finishing.Focus identity before → R.Report → Script Result
  finishSelected identity selected report = ask clock (λ observed → commit
    (S.Finishing.replace identity selected
      (finishMetadata observed report (S.Finishing.Focus.value selected))))

  foundFinish : Id → R.Report → List R.Trace → Script Result
  foundFinish identity report before with S.Finishing.find identity before
  ... | S.Finishing.missing absent = done (failed (toList "diagnostic trace is missing"))
  ... | S.Finishing.found selected = finishSelected identity selected report

  finish : Id → R.Report → Script Result
  finish identity report = ask readDiagnostics λ where
    (inj₁ problem) → done (failed problem)
    (inj₂ before) → foundFinish identity report before

  data Acknowledged : List Event → Set where
    last : ∀ values → Acknowledged ((writeDiagnostics values , inj₂ tt) ∷ [])
    earlier : ∀ event {events} → Acknowledged events → Acknowledged (event ∷ events)

  Safe : Script Result → Set
  Safe program = ∀ events → Runs program events completed → Acknowledged events

  commitSafe : ∀ values → Safe (commit values)
  commitSafe values events (replied _ _ (inj₁ problem) ())
  commitSafe values events (replied _ _ (inj₂ tt) (returned .completed)) = last values

  foundEventSafe : ∀ identity event before → Safe (foundEvent identity event before)
  foundEventSafe identity event before events run with S.Recording.find identity before
  ... | S.Recording.missing absent with run
  ...   | ()
  foundEventSafe identity event before events run | S.Recording.found selected =
    commitSafe (S.Recording.replace identity selected
      (append event (S.Recording.Focus.value selected))) events run

  eventRequiresWriteReceipt : ∀ identity event → Safe (recordEvent identity event)
  eventRequiresWriteReceipt identity event events (replied _ _ (inj₁ problem) ())
  eventRequiresWriteReceipt identity event events (replied _ _ (inj₂ before) later) =
    earlier (readDiagnostics , inj₂ before) (foundEventSafe identity event before _ later)

  finishSelectedSafe : ∀ identity {before} (selected : S.Finishing.Focus identity before) report →
    Safe (finishSelected identity selected report)
  finishSelectedSafe identity selected report events (replied _ _ observed later) =
    earlier (clock , observed) (commitSafe (S.Finishing.replace identity selected
      (finishMetadata observed report (S.Finishing.Focus.value selected))) _ later)

  foundFinishSafe : ∀ identity report before → Safe (foundFinish identity report before)
  foundFinishSafe identity report before events run with S.Finishing.find identity before
  ... | S.Finishing.missing absent with run
  ...   | ()
  foundFinishSafe identity report before events run | S.Finishing.found selected =
    finishSelectedSafe identity selected report events run

  finishRequiresWriteReceipt : ∀ identity report → Safe (finish identity report)
  finishRequiresWriteReceipt identity report events (replied _ _ (inj₁ problem) ())
  finishRequiresWriteReceipt identity report events (replied _ _ (inj₂ before) later) =
    earlier (readDiagnostics , inj₂ before) (foundFinishSafe identity report before _ later)
