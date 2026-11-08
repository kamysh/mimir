{-# OPTIONS --safe #-}
-- Whole review batch: handshake, retained deferrals, selection, one shared
-- account, every selected revision's final readback, finalization.
-- A revision effect includes its concrete scoped-tool/controller trace.
module Mimir.JudgeWorkflow where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (toList)
open import Mimir.Text using (Text)
import Mimir.Effects as Effects
import Mimir.JudgeHandshake as Handshake
import Mimir.JudgeSelection as Selection
import Mimir.JudgeRevision as Revision
import Mimir.JudgeAccounting as Budget
import Mimir.ProviderQueue as Queue
import Mimir.JudgeBatchReadback as Readback
import Mimir.JudgeFinalization as Finalization
import Mimir.JudgeStateRecords as Records
import Mimir.ReviewObservation as Observation
import Mimir.PublicEncoding as Encoding
import Mimir.StandardLibrary as Conversion
import Mimir.SourceFailure as Source
import Mimir.Validation as Validation

module R = Records.Over ℕ

module Run (conversion : Conversion.Contract) (format : Encoding.Formatting)
  (display : Revision.Display) (contract model batchLimit : ℕ)
  (project : Maybe Text) (deliveryMode : Finalization.NotificationMode) where

  initial = Budget.counts 0 0
  module One selected = Revision.Run conversion format display initial selected

  record RevisionReceipt (selected : Observation.Snapshot)
    (currentAccount : Queue.Account initial) (report : R.Report) : Set where
    constructor reviewed
    module T = One selected
    field outcome : T.Outcome
          events : List (Maybe T.P.Event)
          executed : T.Trace (T.start currentAccount report) events (T.finished outcome)

  data Effect : Set where
    clock : Effect
    startClient : Effect
    selection : Selection.Effect → Effect
    beginTrace : R.Report → Effect
    revision : Handshake.Contract.Ready contract model → Observation.Snapshot → Queue.Account initial → R.Report → Effect
    readback : Readback.Effect → Effect
    finalize : Finalization.Effect → Effect

  Reply : Effect → Set
  Reply clock = Maybe ℕ
  Reply startClient = Revision.Error ⊎ Handshake.Contract.Ready contract model
  Reply (selection effect) = Selection.Reply effect
  Reply (beginTrace report) = Text ⊎ ℕ
  Reply (revision clientReady selected currentAccount report) = RevisionReceipt selected currentAccount report
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
  finish report = liftFinalization (Finalization.finishWith deliveryMode report)

  failed : R.Report → Text → Revision.Error → Script R.Report
  failed report reason failureValue = finish (record (R.captureSource (Revision.Error.source failureValue) report)
    { status = toList "blocked" ; blockReason = just reason
    ; failureDetail = just (Revision.Error.detail failureValue) })

  finalReads : List Observation.Pin → R.Report → Bool → Script R.Report
  finalReads original report failure = liftReadback (Readback.finish original report failure
    (map (λ d → Observation.deferred (R.Deferred.identity d) (R.Deferred.revision d))
      (R.Report.deferredReviews report))) >>= finish

  mutual
    revisions : Handshake.Contract.Ready contract model → List Observation.Pin → List Observation.Snapshot → Queue.Account initial → R.Report → Script R.Report
    revisions clientReady original [] currentAccount report = finalReads original report false
    revisions clientReady original (selected ∷ rest) currentAccount report =
      ask (revision clientReady selected currentAccount report) (afterRevision clientReady original rest selected currentAccount report)

    afterRevision : Handshake.Contract.Ready contract model → List Observation.Pin → List Observation.Snapshot →
      (selected : Observation.Snapshot) → (currentAccount : Queue.Account initial) → (report : R.Report) →
      RevisionReceipt selected currentAccount report → Script R.Report
    afterRevision clientReady original rest selected currentAccount report receipt
      with One.Outcome.fatal result | One.Outcome.failed result
      where result = RevisionReceipt.outcome receipt
    ... | true | _ = finish (One.Outcome.report result)
      where result = RevisionReceipt.outcome receipt
    ... | false | true = finalReads original (One.Outcome.report result) true
      where result = RevisionReceipt.outcome receipt
    ... | false | false = revisions clientReady original rest (One.Outcome.account result) (One.Outcome.report result)
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
      { selected = length batch ; selectedIds = map Observation.Pin.identity pins
      ; deferredReviews = map (λ d → R.deferred (Observation.Deferred.identity d) (Observation.Deferred.revision d))
          (Select.Prepared.deferred preparedBatch) }
    dispatch : Select.Disposition → Script R.Report
    dispatch Select.idle = finish (record updated { status = toList "idle" })
    dispatch Select.held = finish (record updated
      { status = toList "blocked" ; blockReason = just (toList "review_deferred") })
    dispatch Select.review = ask (beginTrace updated) λ where
      (inj₁ failureValue) → failed updated (toList "diagnostics_write_error") (Revision.error failureValue nothing)
      (inj₂ traceID) → revisions clientReady pins batch
        (Queue.startAccount initial) (record updated { diagnosticsId = just traceID })

  afterClient : R.Report → Reply startClient → Script R.Report
  afterClient report (inj₁ failureValue) = failed report (toList "mcp_or_configuration_error") failureValue
  afterClient report (inj₂ clientReady) = liftSelection
    (Selection.Select.start contract model batchLimit project clientReady) >>= selectedBatch clientReady report

  start : Script R.Report
  start = ask clock (λ observed → ask startClient
    (afterClient (R.newReport observed (toList "blocked") 0 0 0 0 0)))

  -- Every finite prefix is defined, including interruption during a provider
  -- or transport effect. No or account is recreated between items.
  Runs = P.Runs start
  Prefix = P.Prefix start
