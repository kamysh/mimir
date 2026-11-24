{-# OPTIONS --safe #-}
-- Whole review batch: handshake, retained deferrals, selection, each selected
-- revision's final readback, and finalization.
-- A revision effect includes its concrete scoped-tool/controller trace.
module Mimir.JudgeWorkflow where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_; _++_; map; foldl; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.String using (toList)
open import Mimir.Text using (Text)
import Mimir.Effects as Effects
import Mimir.JudgeHost as Host
import Mimir.JudgeRevisionPolicy as Recovery
open import Relation.Nullary using (does)
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
    openRepair : Recovery.Case → Text → Effect
    selection : Selection.Effect → Effect
    revision : Handshake.Contract.Ready contract model → Observation.Snapshot → R.Report → Effect
    readback : Readback.Effect → Effect
    finalize : Finalization.Effect → Effect

  Reply : Effect → Set
  Reply clock = Maybe ℕ
  Reply (openRepair problem _) = Recovery.CaseWriteError ⊎ Recovery.Publication problem
  Reply startClient = Revision.Error ⊎ Handshake.Contract.Ready contract model
  Reply (selection effect) = Selection.Reply effect
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

  finalizeWith : Host.Continuation → (report : R.Report) →
    Maybe (Acknowledgement.BatchEvidence (R.Report.selectedIds report)) → Script Host.Batch
  finalizeWith next report confirmation =
    liftFinalization (Finalization.finish report confirmation) >>= λ observed → done (Host.batch observed next)

  failed : Host.Remedy → R.Report → Text → Revision.Error → Script Host.Batch
  failed remedy report reason failureValue = finalizeWith (Host.whenCorrected remedy)
    (record (R.captureSource (Revision.Error.source failureValue) report)
      { status = toList "blocked" ; blockReason = just reason
      ; failureDetail = just (Revision.Error.detail failureValue) }) nothing

  finalReads : Host.Continuation → List Observation.Pin → R.Report → Bool → Script Host.Batch
  finalReads next original report failure = liftReadback (Readback.finish original report failure
    (map (λ d → Observation.deferred (R.Deferred.identity d) (R.Deferred.revision d))
      (R.Report.deferredReviews report))) >>= λ checked →
      finalizeWith next (Readback.Readback.observed checked) (Readback.Readback.confirmation checked)

  data Disposition : Set where
    nextReview heldForRepair : Disposition
    later : Recovery.Entry → Disposition
    shared : Host.Continuation → Disposition

  -- Saving a repair case and making its email eligible are one operation.
  -- Its repair command addresses this pin. A failure to save that case
  -- leaves the original source pending and enters database recovery.
  handle : Observation.Pin → Recovery.Turn → Recovery.Obstacle → Recovery.Next → Script Disposition
  handle chosen turn obstacle Recovery.finished = done nextReview
  handle chosen turn obstacle Recovery.enqueueFresh = done (later (Recovery.entry chosen Recovery.fresh))
  handle chosen turn obstacle (Recovery.onProvider (Recovery.resetAt time)) = done (shared (Host.whenProviderResets time))
  handle chosen turn obstacle (Recovery.onProvider Recovery.providerAvailable) = done (shared Host.whenProviderAvailable)
  handle chosen turn obstacle Recovery.readAgain = done (later (Recovery.job chosen turn (Recovery.verifyOutcome obstacle)))
  handle chosen turn obstacle (Recovery.correctBackend detail) = done (shared (Host.whenCorrected (Host.selectWorkingBackend detail)))
  handle chosen turn obstacle (Recovery.askOperator choice) = ask (openRepair (Recovery.repair chosen choice) (Recovery.instructions choice)) λ where
    (inj₁ (Recovery.disconnected detail)) → done (shared Host.whenDatabaseReturns)
    (inj₁ (Recovery.refused detail)) → done (shared (Host.whenCorrected (Host.restoreDatabaseSetup detail)))
    (inj₂ (Recovery.verificationNeeded _ _)) → done heldForRepair
    (inj₂ (Recovery.opened _ _ _ _)) → done heldForRepair
    (inj₂ (Recovery.rescued _ _ _)) → done nextReview
    (inj₂ (Recovery.superseded _ _ _ _)) → done nextReview
    (inj₂ Recovery.removed) → done nextReview

  decide : Observation.Pin → Recovery.Turn → Recovery.Obstacle → Script Disposition
  decide chosen turn obstacle = ask (readback (Readback.getExperience chosen)) readResult
    where
    observed : Observation.Receipt chosen → Script Disposition
    observed receipt = handle chosen turn obstacle (Recovery.afterRead turn obstacle receipt)
    readResult : Readback.Reply (Readback.getExperience chosen) → Script Disposition
    readResult (inj₁ problem) = handle chosen turn obstacle Recovery.readAgain
    readResult (inj₂ nothing) = done nextReview
    readResult (inj₂ (just row)) = observed (Observation.observe chosen (just row))

  -- Capture the work ahead of the failed reviews once. New arrivals cannot
  -- postpone their fresh turns. Each turn still has its own bounded batch.
  schedule : (clientReady : Handshake.Contract.Ready contract model) → Recovery.Selection →
    List Recovery.Entry → R.Report → Script Host.Continuation
  schedule clientReady mode [] report = done Host.scan
  schedule clientReady (Recovery.runEntry _) retries@(_ ∷ _) report =
    done (Host.scheduled retries)
  schedule clientReady Recovery.scanQueue retries@(_ ∷ _) report =
    ask (selection Selection.previousDeferred) readCases
    where
    module AllReady = Selection.Select contract model nothing project clientReady
    failedPins = map (λ item → let chosen = Recovery.Entry.selected item in
      Observation.deferred (Observation.Pin.identity chosen) (Observation.Pin.sourceRevision chosen)) retries
    dispatch : AllReady.Result → Script Host.Continuation
    dispatch (AllReady.failed remedy failure) = done (Host.whenCorrected remedy)
    dispatch (AllReady.malformed fault) = done (Host.whenCorrected
      (Host.restoreToolClient (Validation.Fault.explanation fault)))
    dispatch (AllReady.selected ready) = done (Host.scheduled
      (foldl Recovery.requeue (map (λ chosen → Recovery.entry chosen Recovery.first) (AllReady.pins ready)) retries))

    readCases : Selection.Reply Selection.previousDeferred → Script Host.Continuation
    readCases (inj₁ failure) = done (Host.whenCorrected (Host.restoreDatabaseSetup (Revision.Error.detail failure)))
    readCases (inj₂ held) = liftSelection (AllReady.reconcile held failedPins) >>= dispatch

  phase : Recovery.Selection → Recovery.Turn
  phase Recovery.scanQueue = Recovery.first
  phase (Recovery.runEntry item) = Recovery.Entry.turn item

  mutual
    revisions : Handshake.Contract.Ready contract model → Recovery.Selection → List Observation.Pin →
      List Observation.Snapshot → List Recovery.Entry → R.Report → Script Host.Batch
    revisions clientReady mode original [] retries report =
      schedule clientReady mode retries report >>= λ next → finalReads next original report false
    revisions clientReady mode original (selected ∷ rest) retries report =
      ask (revision clientReady selected report) (afterRevision clientReady mode original rest selected retries report)

    afterRevision : Handshake.Contract.Ready contract model → Recovery.Selection → List Observation.Pin →
      List Observation.Snapshot → (selected : Observation.Snapshot) → List Recovery.Entry →
      (report : R.Report) → RevisionReceipt selected report → Script Host.Batch
    afterRevision clientReady mode original rest selected retries report receipt = withClient
      (toolStopped selected (RevisionReceipt.events receipt))
      where
      result = RevisionReceipt.outcome receipt
      updated = One.Outcome.report result
      chosen = Observation.pinSnapshot selected
      proceed : Handshake.Contract.Ready contract model → Disposition → Script Host.Batch
      proceed client heldForRepair = revisions client mode original rest retries (record updated
        { deferredReviews = R.Report.deferredReviews updated ++
          R.deferred (Observation.Pin.identity chosen) (Observation.Pin.sourceRevision chosen) ∷ [] })
      proceed client nextReview = revisions client mode original rest retries updated
      proceed client (later item) = revisions client mode original rest (Recovery.requeue retries item) updated
      proceed client (shared next) = finalReads next original updated true
      resume : Handshake.Contract.Ready contract model → Script Host.Batch
      resume client with One.Outcome.obstacle result
      ... | nothing = proceed client nextReview
      ... | just obstacle = decide chosen (phase mode) obstacle >>= proceed client
      withClient : Bool → Script Host.Batch
      withClient false = resume clientReady
      withClient true = ask startClient λ where
        (inj₁ failure) → failed (Host.restoreToolClient (Revision.Error.detail failure))
          updated (toList "mcp_restart_failed") failure
        (inj₂ client) → resume client

  selectedBatch : (clientReady : Handshake.Contract.Ready contract model) → R.Report →
    Selection.Select.Result contract model batchLimit project clientReady → Script Host.Batch
  selectedBatch clientReady report (Selection.Select.failed remedy failureValue) =
    failed remedy report (toList "mcp_or_configuration_error") failureValue
  selectedBatch clientReady report (Selection.Select.malformed failureValue) =
    failed (Host.restoreToolClient (Validation.Fault.explanation failureValue)) report (toList "mcp_or_configuration_error") (Revision.error (Validation.Fault.explanation failureValue) nothing)
  selectedBatch clientReady report (Selection.Select.selected preparedBatch) = dispatch (Select.disposition preparedBatch)
    where
    module Select = Selection.Select contract model batchLimit project clientReady
    batch = Select.Prepared.batch preparedBatch
    pins = Select.pins preparedBatch
    updated = record report
      { selectedIds = map Observation.Pin.identity pins
      ; deferredReviews = map (λ d → R.deferred (Observation.Deferred.identity d) (Observation.Deferred.revision d))
          (Select.Prepared.deferred preparedBatch) }
    dispatch : Select.Disposition → Script Host.Batch
    dispatch Select.idle = finalizeWith Host.whenWorkArrives (record updated { status = toList "idle" }) nothing
    dispatch Select.held = finalizeWith Host.whenWorkArrives (record updated
      { status = toList "blocked" ; blockReason = just (toList "review_deferred") }) nothing
    dispatch Select.review = revisions clientReady Recovery.scanQueue pins batch [] updated

  pinned : Handshake.Contract.Ready contract model → Recovery.Entry → R.Report → Script Host.Batch
  pinned clientReady item before = ask (selection Selection.previousDeferred) checkCase
    where
    chosen = Recovery.Entry.selected item
    chosenID = Observation.Pin.identity chosen
    -- An obsolete turn produces no batch failure and no fabricated review.
    report = record before { status = toList "idle" }
    turn = Recovery.Entry.turn item
    finishTurn : Disposition → Script Host.Batch
    finishTurn heldForRepair = finalizeWith Host.scan (record report
      { deferredReviews = R.deferred chosenID (Observation.Pin.sourceRevision chosen) ∷ []
      ; status = toList "blocked" ; blockReason = just (toList "review_requires_repair") }) nothing
    finishTurn nextReview = finalizeWith Host.scan report nothing
    finishTurn (later queued) = finalizeWith (Host.scheduled (queued ∷ []))
      (record report { status = toList "partial" ; selectedIds = chosenID ∷ [] }) nothing
    finishTurn (shared next) = finalizeWith next (record report { status = toList "blocked" }) nothing
    readProblem : Text → Script Host.Batch
    readProblem detail with Recovery.Entry.task item
    ... | Recovery.prepare = finishTurn (later (Recovery.job chosen turn Recovery.verifySource))
    ... | _ = handle chosen turn (Recovery.toolStopped detail)
        (Recovery.askOperator (Recovery.restoreReadAccess detail)) >>= finishTurn
    runPending : Observation.Snapshot → Script Host.Batch
    runPending row with Recovery.Entry.task item
    ... | Recovery.verifyOutcome obstacle = handle chosen turn obstacle (Recovery.pending turn obstacle) >>= finishTurn
    ... | Recovery.verifySource = finishTurn (later (Recovery.entry chosen turn))
    ... | Recovery.prepare = revisions clientReady (Recovery.runEntry item) (chosen ∷ []) (row ∷ []) []
        (record report { selectedIds = Observation.Pin.identity chosen ∷ [] })
    admitted : (row : Observation.Snapshot) → Observation.Receipt chosen → Script Host.Batch
    admitted row (Observation.malformed fault) = readProblem (Validation.Fault.explanation fault)
    admitted row (Observation.found _ _ (Observation.pending _ _ _)) with Selection.inScope project row ∧
      does (Observation.stillDeferred? (Observation.deferred chosenID (Observation.Pin.sourceRevision chosen)) row)
    ... | true = runPending row
    ... | false = finalizeWith Host.scan report nothing
    admitted row _ = finalizeWith Host.scan report nothing
    readResult : Selection.Reply (Selection.current chosenID) → Script Host.Batch
    readResult (inj₁ problem) = readProblem (Revision.Error.detail problem)
    readResult (inj₂ nothing) = finalizeWith Host.scan report nothing
    readResult (inj₂ (just row)) = admitted row (Observation.observe chosen (just row))
    checkCase : Selection.Reply Selection.previousDeferred → Script Host.Batch
    checkCase (inj₁ problem) = failed (Host.restoreDatabaseSetup (Revision.Error.detail problem))
      report (toList "repair_cases_unavailable") problem
    checkCase (inj₂ held) with Recovery.held chosen held
    ... | true = finalizeWith Host.scan report nothing
    ... | false = ask (selection (Selection.current chosenID)) readResult

  afterClient : Recovery.Selection → R.Report → Reply startClient → Script Host.Batch
  afterClient mode report (inj₁ failureValue) = failed (Host.restoreToolClient (Revision.Error.detail failureValue))
    report (toList "mcp_or_configuration_error") failureValue
  afterClient Recovery.scanQueue report (inj₂ clientReady) = liftSelection
    (Selection.Select.start contract model batchLimit project clientReady) >>= selectedBatch clientReady report
  afterClient (Recovery.runEntry item) report (inj₂ clientReady) = pinned clientReady item report

  start : Recovery.Selection → Script Host.Batch
  start mode = ask clock (λ observed → ask startClient
    (afterClient mode (R.newReport observed (toList "blocked"))))

  -- Every finite prefix is defined, including interruption during a provider
  -- or transport effect.
  Runs = λ mode → P.Runs (start mode)
  Prefix = λ mode → P.Prefix (start mode)
