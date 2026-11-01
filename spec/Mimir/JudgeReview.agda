{-# OPTIONS --safe #-}
-- One selected immutable experience revision. Model completion, tool success,
-- and database confirmation are distinct events. Every attempt is counted.
-- Trace persistence is a barrier before the next external request.
module Mimir.JudgeReview where

open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Empty using (⊥-elim)
open import Mimir.Validation using (Fault)
open import Mimir.ReviewObservation using (Pin)
open import Mimir.JudgeAcknowledgement using (Evidence)
import Mimir.McpErrors as Mcp

-- Payload is the already parsed wire value; its full schema and scope checks
-- belong to the tool dispatcher. They must return a typed validation fault.
module Controller (Payload : Set) (selected : Pin) where
  open import Mimir.JudgeAccounting public using (Counts; counts)
  open import Mimir.JudgeTools public using (query; review) renaming (Kind to ToolKind)
  record Call : Set where
    constructor call
    field kind : ToolKind; arguments : Payload

  data Feedback : Set where
    initial : Feedback
    value : Payload → Feedback
    rejected : Fault → Feedback
    uncertainCommit : Feedback
    indeterminateFailure : Mcp.Error → Feedback

  data Result : Set where
    confirmed : Evidence selected → Result
    sourceChanged unreviewed
      transportInterrupted transportFailed serviceFailed traceFailed stopped : Result

  data Purpose : Set where
    afterReview afterLoss afterDone : Purpose
    afterIndeterminate : Mcp.Error → Purpose

  data Trace : Set where
    modelRequested toolRequested toolReturned modelSaidDone
      interruptionObserved transportLost receiptPending
      receiptConfirmed receiptChanged receiptUnavailable : Trace
    inputRejected : Fault → Trace
    unclassifiedFailure : Mcp.Error → Trace

  -- Continuations are finite states, not arbitrary functions supplied by a
  -- worker. A log acknowledgement can only resume the stored continuation.
  data Continue : Set where
    ask : Counts → Feedback → Continue
    invoke : Counts → Call → Continue
    observe : Counts → Purpose → Continue
    reconsider : Counts → Feedback → Continue
    finish : Result → Continue

  data State : Set where
    ready : Counts → Feedback → State
    tracing : Trace → Continue → State
    modelPending : Counts → State
    toolPending : Counts → Call → State
    receiptPending : Counts → Purpose → State
    finished : Result → State

  data Effect : Set where
    persist : Trace → Effect
    requestModel : Feedback → Effect
    requestTool : Call → Effect
    readSelectedRevision : Effect
    cancelOwnedRequests : Effect

  data ModelAction : Set where
    done : ModelAction
    useTool : Call → ModelAction
    malformed : Fault → ModelAction

  data ToolReply : Set where
    returned : Payload → ToolReply
    refused : Fault → ToolReply
    lost : ToolReply
    indeterminate : Mcp.Error → ToolReply

  data Receipt : Set where
    acknowledged : Evidence selected → Receipt
    changed pending unavailable : Receipt

  data Input : Set where
    tick traceWritten traceWriteFailed interrupted stop : Input
    modelReply : ModelAction → Input
    queuedTool : Call → Input
    queuedMalformed : Fault → Input
    toolReply : ToolReply → Input
    receipt : Receipt → Input

  record Step : Set where
    constructor next
    field state : State; effects : List Effect
  open Step

  log : Trace → Continue → Step
  log event continuation = next (tracing event continuation) (persist event ∷ [])

  resume : Continue → Step
  resume (ask fuel feedback) = next (modelPending fuel) (requestModel feedback ∷ [])
  resume (invoke fuel request) = next (toolPending fuel request) (requestTool request ∷ [])
  resume (observe fuel purpose) = next (receiptPending fuel purpose) (readSelectedRevision ∷ [])
  resume (reconsider fuel feedback) = next (ready fuel feedback) []
  resume (finish result) = next (finished result) []

  pendingReceipt : Counts → Purpose → Step
  pendingReceipt fuel afterReview = log receiptPending (reconsider fuel initial)
  pendingReceipt fuel afterLoss = log receiptPending (reconsider fuel uncertainCommit)
  pendingReceipt fuel afterDone = log receiptPending (finish unreviewed)
  pendingReceipt fuel (afterIndeterminate failure) =
    log receiptPending (reconsider fuel (indeterminateFailure failure))

  -- Stop takes precedence in every state, including an outstanding log write.
  step : State → Input → Step
  step state stop = next (finished stopped) (cancelOwnedRequests ∷ [])
  step (ready (counts models tools) feedback) tick =
    log modelRequested (ask (counts (suc models) tools) feedback)
  step (tracing event continuation) traceWritten = resume continuation
  step (tracing event continuation) traceWriteFailed = next (finished traceFailed) []
  step (modelPending fuel) (modelReply done) = log modelSaidDone (observe fuel afterDone)
  step (modelPending (counts models tools)) (modelReply (useTool request)) =
    log toolRequested (invoke (counts models (suc tools)) request)
  step (modelPending (counts models tools)) (modelReply (malformed failure)) =
    log (inputRejected failure) (reconsider (counts models (suc tools)) (rejected failure))
  step (ready (counts models tools) feedback) (queuedTool request) =
    log toolRequested (invoke (counts models (suc tools)) request)
  step (ready (counts models tools) feedback) (queuedMalformed failure) =
    log (inputRejected failure) (reconsider (counts models (suc tools)) (rejected failure))
  step (toolPending fuel (call (query operation) arguments)) (toolReply (returned payload)) =
    log toolReturned (reconsider fuel (value payload))
  step (toolPending fuel (call review arguments)) (toolReply (returned payload)) =
    log toolReturned (observe fuel afterReview)
  step (toolPending fuel request) (toolReply (refused failure)) =
    log (inputRejected failure) (reconsider fuel (rejected failure))
  step (toolPending fuel (call (query operation) arguments)) (toolReply lost) =
    log transportLost (finish transportFailed)
  step (toolPending fuel (call review arguments)) (toolReply lost) =
    log transportLost (observe fuel afterLoss)
  step (toolPending fuel (call (query operation) arguments)) (toolReply (indeterminate failure)) =
    log (unclassifiedFailure failure) (finish serviceFailed)
  step (toolPending fuel (call review arguments)) (toolReply (indeterminate failure)) =
    log (unclassifiedFailure failure) (observe fuel (afterIndeterminate failure))
  step (receiptPending fuel purpose) (receipt (acknowledged proof)) = log receiptConfirmed (finish (confirmed proof))
  step (receiptPending fuel purpose) (receipt changed) = log receiptChanged (finish sourceChanged)
  step (receiptPending fuel purpose) (receipt pending) = pendingReceipt fuel purpose
  step (receiptPending fuel purpose) (receipt unavailable) = log receiptUnavailable (finish transportFailed)
  step (modelPending fuel) interrupted = log interruptionObserved (finish transportInterrupted)
  step (toolPending fuel (call (query operation) arguments)) interrupted = log interruptionObserved (finish transportInterrupted)
  step (toolPending fuel (call review arguments)) interrupted = log interruptionObserved (observe fuel afterLoss)
  step (receiptPending fuel purpose) interrupted = log interruptionObserved (finish transportInterrupted)
  step (tracing event continuation) interrupted = next (finished traceFailed) []
  step state input = next state []

  after : State → List Input → State
  after state [] = state
  after state (input ∷ rest) = after (Step.state (step state input)) rest

  stopImmediately : ∀ state →
    step state stop ≡ next (finished stopped) (cancelOwnedRequests ∷ [])
  stopImmediately state = refl

  -- A successful tool return still requires an independent database read.
  toolSuccessNeedsReceipt : ∀ fuel arguments payload →
    step (toolPending fuel (call review arguments)) (toolReply (returned payload)) ≡
    log toolReturned (observe fuel afterReview)
  toolSuccessNeedsReceipt fuel arguments payload = refl

  -- The model saying 'done' never establishes a confirmed review.
  modelDoneNeedsReceipt : ∀ fuel →
    step (modelPending fuel) (modelReply done) ≡ log modelSaidDone (observe fuel afterDone)
  modelDoneNeedsReceipt fuel = refl

  -- A validation refusal reaches the next model call unchanged, after its
  -- diagnostic is persisted. There is no generic-error substitution.
  rejectionDelivered : ∀ models tools request failure →
    step (after (toolPending (counts models tools) request)
      (toolReply (refused failure) ∷ traceWritten ∷ tick ∷ [])) traceWritten ≡
    next (modelPending (counts (suc models) tools)) (requestModel (rejected failure) ∷ [])
  rejectionDelivered models tools (call (query operation) arguments) failure = refl
  rejectionDelivered models tools (call review arguments) failure = refl

  -- Invalid model arguments record a tool attempt and a subsequent model
  -- request records a model attempt, exactly as valid requests do.
  malformedCountsBoth : ∀ models tools failure →
    step (after (modelPending (counts models tools))
      (modelReply (malformed failure) ∷ traceWritten ∷ tick ∷ [])) traceWritten ≡
    next (modelPending (counts (suc models) (suc tools))) (requestModel (rejected failure) ∷ [])
  malformedCountsBoth models tools failure = refl

  everyModelRequestAdmitted : ∀ models tools feedback →
    step (ready (counts models tools) feedback) tick ≡
      log modelRequested (ask (counts (suc models) tools) feedback)
  everyModelRequestAdmitted models tools feedback = refl

  everyToolRequestAdmitted : ∀ models tools request →
    step (modelPending (counts models tools)) (modelReply (useTool request)) ≡
      log toolRequested (invoke (counts models (suc tools)) request)
  everyToolRequestAdmitted models tools request = refl

  lostCommitReadFirst : ∀ fuel arguments →
    step (after (toolPending fuel (call review arguments)) (toolReply lost ∷ [])) traceWritten ≡
    next (receiptPending fuel afterLoss) (readSelectedRevision ∷ [])
  lostCommitReadFirst fuel arguments = refl

  -- A trace failure cannot silently proceed with the pending external action.
  failedTraceStops : ∀ event continuation →
    step (tracing event continuation) traceWriteFailed ≡ next (finished traceFailed) []
  failedTraceStops event continuation = refl

  queuedCallPreservesProviderCount : ∀ models tools feedback request →
    step (ready (counts models tools) feedback) (queuedTool request) ≡
    log toolRequested (invoke (counts models (suc tools)) request)
  queuedCallPreservesProviderCount models tools feedback request = refl

  queuedMalformedPreservesProviderCount : ∀ models tools feedback failure →
    step (ready (counts models tools) feedback) (queuedMalformed failure) ≡
    log (inputRejected failure) (reconsider (counts models (suc tools)) (rejected failure))
  queuedMalformedPreservesProviderCount models tools feedback failure = refl

  unclassifiedReviewRequiresReceipt : ∀ fuel arguments failure →
    step (toolPending fuel (call review arguments)) (toolReply (indeterminate failure)) ≡
    log (unclassifiedFailure failure) (observe fuel (afterIndeterminate failure))
  unclassifiedReviewRequiresReceipt fuel arguments failure = refl

  pendingUnclassifiedFailureRetainsCause : ∀ fuel failure →
    pendingReceipt fuel (afterIndeterminate failure) ≡
    log receiptPending (reconsider fuel (indeterminateFailure failure))
  pendingUnclassifiedFailureRetainsCause fuel failure = refl
