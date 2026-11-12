{-# OPTIONS --safe #-}
-- Whole review batch: handshake, retained deferrals, selection, each selected
-- revision's final readback, and finalization.
-- A revision effect includes its concrete scoped-tool/controller trace.
module Mimir.JudgeWorkflow where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.String using (toList)
open import Mimir.Text using (Text)
import Mimir.Effects as Effects
import Mimir.JudgeHandshake as Handshake
import Mimir.JudgeSelection as Selection
import Mimir.JudgeRevision as Revision
import Mimir.JudgeBatchReadback as Readback
import Mimir.JudgeFinalization as Finalization
import Mimir.JudgeStateRecords as Records
import Mimir.ReviewObservation as Observation
import Mimir.JudgeAcknowledgement as Acknowledgement
import Mimir.PublicEncoding as Encoding
import Mimir.StandardLibrary as Conversion
import Mimir.SourceFailure as Source
import Mimir.Validation as Validation

open import Mimir.UUIDGroups using (UUID)

module R = Records.Over UUID

module Run (conversion : Conversion.Contract) (format : Encoding.Formatting)
  (display : Revision.Display) (contract model : ℕ) (batchLimit : Maybe ℕ)
  (project : Maybe Text) where

  module One selected = Revision.Run conversion format display selected

  record RevisionReceipt (selected : Observation.Snapshot) (report : R.Report) : Set where
    constructor reviewed
    module T = One selected
    field outcome : T.Outcome
          events : List (Maybe T.P.Event)
          executed : T.Trace (T.start report) events (T.finished outcome)

  toolStopped : (selected : Observation.Snapshot) → List (Maybe (One.P.Event selected)) → Bool
  toolStopped selected [] = false
  toolStopped selected (just (One.stopTool , tt) ∷ rest) = true
  toolStopped selected (_ ∷ rest) = toolStopped selected rest

  data Effect : Set where
    clock : Effect
    startClient : Effect
    selection : Selection.Effect → Effect
    beginTrace : R.Report → Effect
    reportTraceProblem : Text → Effect
    revision : Handshake.Contract.Ready contract model → Observation.Snapshot → R.Report → Effect
    readback : Readback.Effect → Effect
    finalize : Finalization.Effect → Effect

  Reply : Effect → Set
  Reply clock = Maybe ℕ
  Reply startClient = Revision.Error ⊎ Handshake.Contract.Ready contract model
  Reply (selection effect) = Selection.Reply effect
  Reply (beginTrace report) = Text ⊎ UUID
  Reply (reportTraceProblem failure) = ⊤
  Reply (revision clientReady selected report) = RevisionReceipt selected report
  Reply (readback effect) = Readback.Reply effect
  Reply (finalize effect) = Finalization.Reply effect
  module P = Effects.Protocol Effect Reply
  open P using (Script; done; ask; _>>=_)

  liftSelection : ∀ {A} → Selection.E.Script A → Script A
  liftSelection (Selection.E.done value) = done value
  liftSelection (Selection.E.ask effect next) = ask (selection effect) (λ reply → liftSelection (next reply))

  liftReadback : ∀ {A} → Readback.E.Script A → Script A
  liftReadback (Readback.E.done value) = done value
  liftReadback (Readback.E.ask effect next) = ask (readback effect) (λ reply → liftReadback (next reply))

  liftFinalization : ∀ {A} → Finalization.E.Script A → Script A
  liftFinalization (Finalization.E.done value) = done value
  liftFinalization (Finalization.E.ask effect next) = ask (finalize effect) (λ reply → liftFinalization (next reply))

  finish : R.Report → Script R.Report
  finish report = liftFinalization (Finalization.finish report nothing)

  finishObserved : (report : R.Report) →
    Maybe (Acknowledgement.BatchEvidence (R.Report.selectedIds report)) → Script R.Report
  finishObserved report confirmation = liftFinalization (Finalization.finish report confirmation)

  failed : R.Report → Text → Revision.Error → Script R.Report
  failed report reason failureValue = finish (record (R.captureSource (Revision.Error.source failureValue) report)
    { status = toList "blocked" ; blockReason = just reason
    ; failureDetail = just (Revision.Error.detail failureValue) })

  finalReads : List Observation.Pin → R.Report → Bool → Script R.Report
  finalReads original report failure = liftReadback (Readback.finish original report failure
    (map (λ d → Observation.deferred (R.Deferred.identity d) (R.Deferred.revision d))
      (R.Report.deferredReviews report))) >>= λ { (observed , confirmation) → finishObserved observed confirmation }

  mutual
    revisions : Handshake.Contract.Ready contract model → List Observation.Pin → List Observation.Snapshot → R.Report → Script R.Report
    revisions clientReady original [] report = finalReads original report false
    revisions clientReady original (selected ∷ rest) report =
      ask (revision clientReady selected report) (afterRevision clientReady original rest selected report)

    afterRevision : Handshake.Contract.Ready contract model → List Observation.Pin → List Observation.Snapshot →
      (selected : Observation.Snapshot) → (report : R.Report) →
      RevisionReceipt selected report → Script R.Report
    afterRevision clientReady original rest selected report receipt
      with One.Outcome.failed result | toolStopped selected (RevisionReceipt.events receipt)
      where result = RevisionReceipt.outcome receipt
    ... | true | true = ask startClient λ where
      (inj₁ failure) → failed (One.Outcome.report (RevisionReceipt.outcome receipt)) (toList "mcp_restart_failed") failure
      (inj₂ _) → finalReads original (One.Outcome.report (RevisionReceipt.outcome receipt)) true
    ... | true | false = finalReads original (One.Outcome.report result) true
      where result = RevisionReceipt.outcome receipt
    ... | false | true = ask startClient λ where
      (inj₁ failure) → failed (One.Outcome.report (RevisionReceipt.outcome receipt)) (toList "mcp_restart_failed") failure
      (inj₂ nextClient) → revisions nextClient original rest (One.Outcome.report (RevisionReceipt.outcome receipt))
    ... | false | false = revisions clientReady original rest (One.Outcome.report result)
      where result = RevisionReceipt.outcome receipt

  selectedBatch : (clientReady : Handshake.Contract.Ready contract model) → R.Report →
    Selection.Select.Result contract model batchLimit project clientReady → Script R.Report
  selectedBatch clientReady report (Selection.Select.failed failureValue) =
    failed report (toList "mcp_or_configuration_error") failureValue
  selectedBatch clientReady report (Selection.Select.malformed failureValue) =
    failed report (toList "mcp_or_configuration_error") (Revision.error (Validation.Fault.explanation failureValue) nothing)
  selectedBatch clientReady report (Selection.Select.selected preparedBatch) = dispatch (Select.disposition preparedBatch)
    where
    module Select = Selection.Select contract model batchLimit project clientReady
    batch = Select.Prepared.batch preparedBatch
    pins = Select.pins preparedBatch
    updated = record report
      { selectedIds = map Observation.Pin.identity pins
      ; deferredReviews = map (λ d → R.deferred (Observation.Deferred.identity d) (Observation.Deferred.revision d))
          (Select.Prepared.deferred preparedBatch) }
    dispatch : Select.Disposition → Script R.Report
    dispatch Select.idle = finish (record updated { status = toList "idle" })
    dispatch Select.held = finish (record updated
      { status = toList "blocked" ; blockReason = just (toList "review_deferred") })
    dispatch Select.review = ask (beginTrace updated) λ where
      (inj₁ failureValue) → ask (reportTraceProblem failureValue) λ _ →
        revisions clientReady pins batch updated
      (inj₂ traceID) → revisions clientReady pins batch (record updated { diagnosticsId = just traceID })

  afterClient : R.Report → Reply startClient → Script R.Report
  afterClient report (inj₁ failureValue) = failed report (toList "mcp_or_configuration_error") failureValue
  afterClient report (inj₂ clientReady) = liftSelection
    (Selection.Select.start contract model batchLimit project clientReady) >>= selectedBatch clientReady report

  start : Script R.Report
  start = ask clock (λ observed → ask startClient
    (afterClient (R.newReport observed (toList "blocked"))))

  -- Every finite prefix is defined, including interruption during a provider
  -- or transport effect.
  Runs = P.Runs start
  Prefix = P.Prefix start
