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
import Mimir.DiagnosticText as Bounded
import Mimir.Validation as Validation

module R = Records.Over ℕ

module Run (conversion : Conversion.Contract) (format : Encoding.Formatting)
  (display : Revision.Display) (contract model batchLimit : ℕ)
  (project : Maybe Text) where

  initial = Budget.counts 0 0
  module One selected = Revision.Run conversion format display initial selected

  record RevisionReceipt (selected : Observation.Snapshot)
    (account : Queue.Account initial) (report : R.Report) : Set where
    constructor reviewed
    module T = One selected
    field outcome : T.Outcome
          events : List (Maybe T.P.Event)
          executed : T.Trace (T.start account report) events (T.finished outcome)

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
  Reply (revision ready selected account report) = RevisionReceipt selected account report
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
  finish report = liftFinalization (Finalization.finish report)

  failed : R.Report → Text → Revision.Error → Script R.Report
  failed report reason error = finish (record (R.captureSource (Revision.Error.source error) report)
    { status = toList "blocked" ; blockReason = just reason
    ; failureDetail = just (Bounded.bounded 512 (Revision.Error.detail error)) })

  finalReads : List Observation.Pin → R.Report → Bool → Script R.Report
  finalReads original report failure = liftReadback (Readback.finish original report failure
    (map (λ d → Observation.deferred (R.Deferred.identity d) (R.Deferred.revision d))
      (R.Report.deferredReviews report))) >>= finish

  mutual
    revisions : Handshake.Contract.Ready contract model → List Observation.Pin → List Observation.Snapshot → Queue.Account initial → R.Report → Script R.Report
    revisions ready original [] account report = finalReads original report false
    revisions ready original (selected ∷ rest) account report =
      ask (revision ready selected account report) (afterRevision ready original rest selected account report)

    afterRevision : Handshake.Contract.Ready contract model → List Observation.Pin → List Observation.Snapshot →
      (selected : Observation.Snapshot) → (account : Queue.Account initial) → (report : R.Report) →
      RevisionReceipt selected account report → Script R.Report
    afterRevision ready original rest selected account report receipt
      with One.Outcome.fatal result | One.Outcome.failed result
      where result = RevisionReceipt.outcome receipt
    ... | true | _ = finish (One.Outcome.report result)
      where result = RevisionReceipt.outcome receipt
    ... | false | true = finalReads original (One.Outcome.report result) true
      where result = RevisionReceipt.outcome receipt
    ... | false | false = revisions ready original rest (One.Outcome.account result) (One.Outcome.report result)
      where result = RevisionReceipt.outcome receipt

  selectedBatch : (ready : Handshake.Contract.Ready contract model) → R.Report →
    Selection.Select.Result contract model batchLimit project ready → Script R.Report
  selectedBatch ready report (Selection.Select.failed error) =
    failed report (toList "mcp_or_configuration_error") error
  selectedBatch ready report (Selection.Select.malformed error) =
    failed report (toList "mcp_or_configuration_error") (Revision.error (Validation.Fault.explanation error) nothing)
  selectedBatch ready report (Selection.Select.selected prepared) = dispatch (Select.disposition prepared)
    where
    module Select = Selection.Select contract model batchLimit project ready
    batch = Select.Prepared.batch prepared
    pins = Select.pins prepared
    updated = record report
      { selected = length batch ; selectedIds = map Observation.Pin.identity pins
      ; deferredReviews = map (λ d → R.deferred (Observation.Deferred.identity d) (Observation.Deferred.revision d))
          (Select.Prepared.deferred prepared) }
    dispatch : Select.Disposition → Script R.Report
    dispatch Select.idle = finish (record updated { status = toList "idle" })
    dispatch Select.held = finish (record updated
      { status = toList "blocked" ; blockReason = just (toList "review_deferred") })
    dispatch Select.review = ask (beginTrace updated) λ where
      (inj₁ error) → failed updated (toList "diagnostics_write_error") (Revision.error error nothing)
      (inj₂ traceID) → revisions ready pins batch
        (Queue.startAccount initial) (record updated { diagnosticsId = just traceID })

  afterClient : R.Report → Reply startClient → Script R.Report
  afterClient report (inj₁ error) = failed report (toList "mcp_or_configuration_error") error
  afterClient report (inj₂ ready) = liftSelection
    (Selection.Select.start contract model batchLimit project ready) >>= selectedBatch ready report

  start : Script R.Report
  start = ask clock (λ observed → ask startClient
    (afterClient (R.newReport observed (toList "blocked") 0 0 0 0 0)))

  -- Every finite prefix is defined, including interruption during a provider
  -- or transport effect. No or account is recreated between items.
  Runs = P.Runs start
  Prefix = P.Prefix start
