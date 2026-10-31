{-# OPTIONS --safe #-}
-- One selected immutable experience revision. Model completion, tool success,
-- and database confirmation are distinct events. Every retry is budgeted.
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
  open import Mimir.JudgeBudget public using (Budget; budget)
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
    sourceChanged unreviewed modelExhausted toolExhausted
      timedOut transportFailed serviceFailed traceFailed stopped : Result

  data Purpose : Set where
    afterReview afterLoss afterDone : Purpose
    afterIndeterminate : Mcp.Error → Purpose

  data Trace : Set where
    modelRequested toolRequested toolReturned modelSaidDone
      modelLimit toolLimit timeoutObserved transportLost receiptPending
      receiptConfirmed receiptChanged receiptUnavailable : Trace
    inputRejected : Fault → Trace
    unclassifiedFailure : Mcp.Error → Trace

  -- Continuations are finite states, not arbitrary functions supplied by a
  -- worker. A log acknowledgement can only resume the stored continuation.
  data Continue : Set where
    ask : Budget → Feedback → Continue
    invoke : Budget → Call → Continue
    observe : Budget → Purpose → Continue
    reconsider : Budget → Feedback → Continue
    finish : Result → Continue

  data State : Set where
    ready : Budget → Feedback → State
    tracing : Trace → Continue → State
    modelPending : Budget → State
    toolPending : Budget → Call → State
    receiptPending : Budget → Purpose → State
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
    tick traceWritten traceWriteFailed timeout stop : Input
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

  pendingReceipt : Budget → Purpose → Step
  pendingReceipt fuel afterReview = log receiptPending (reconsider fuel initial)
  pendingReceipt fuel afterLoss = log receiptPending (reconsider fuel uncertainCommit)
  pendingReceipt fuel afterDone = log receiptPending (finish unreviewed)
  pendingReceipt fuel (afterIndeterminate failure) =
    log receiptPending (reconsider fuel (indeterminateFailure failure))

  -- Stop takes precedence in every state, including an outstanding log write.
  step : State → Input → Step
  step state stop = next (finished stopped) (cancelOwnedRequests ∷ [])
  step (ready (budget zero tools) feedback) tick = log modelLimit (finish modelExhausted)
  step (ready (budget (suc models) tools) feedback) tick =
    log modelRequested (ask (budget models tools) feedback)
  step (tracing event continuation) traceWritten = resume continuation
  step (tracing event continuation) traceWriteFailed = next (finished traceFailed) []
  step (modelPending fuel) (modelReply done) = log modelSaidDone (observe fuel afterDone)
  step (modelPending (budget models zero)) (modelReply (useTool request)) =
    log toolLimit (finish toolExhausted)
  step (modelPending (budget models (suc tools))) (modelReply (useTool request)) =
    log toolRequested (invoke (budget models tools) request)
  step (modelPending (budget models zero)) (modelReply (malformed failure)) =
    log toolLimit (finish toolExhausted)
  step (modelPending (budget models (suc tools))) (modelReply (malformed failure)) =
    log (inputRejected failure) (reconsider (budget models tools) (rejected failure))
  step (ready (budget models zero) feedback) (queuedTool request) = log toolLimit (finish toolExhausted)
  step (ready (budget models (suc tools)) feedback) (queuedTool request) =
    log toolRequested (invoke (budget models tools) request)
  step (ready (budget models zero) feedback) (queuedMalformed failure) = log toolLimit (finish toolExhausted)
  step (ready (budget models (suc tools)) feedback) (queuedMalformed failure) =
    log (inputRejected failure) (reconsider (budget models tools) (rejected failure))
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
  step (modelPending fuel) timeout = log timeoutObserved (finish timedOut)
  step (toolPending fuel (call (query operation) arguments)) timeout = log timeoutObserved (finish timedOut)
  step (toolPending fuel (call review arguments)) timeout = log timeoutObserved (observe fuel afterLoss)
  step (receiptPending fuel purpose) timeout = log timeoutObserved (finish timedOut)
  step (tracing event continuation) timeout = next (finished traceFailed) []
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
    step (after (toolPending (budget (suc models) tools) request)
      (toolReply (refused failure) ∷ traceWritten ∷ tick ∷ [])) traceWritten ≡
    next (modelPending (budget models tools)) (requestModel (rejected failure) ∷ [])
  rejectionDelivered models tools (call (query operation) arguments) failure = refl
  rejectionDelivered models tools (call review arguments) failure = refl

  -- Invalid model arguments consume a tool attempt and a subsequent model
  -- request consumes a model attempt, exactly as valid requests do.
  malformedConsumesBoth : ∀ models tools failure →
    step (after (modelPending (budget (suc models) (suc tools)))
      (modelReply (malformed failure) ∷ traceWritten ∷ tick ∷ [])) traceWritten ≡
    next (modelPending (budget models tools)) (requestModel (rejected failure) ∷ [])
  malformedConsumesBoth models tools failure = refl

  noModelAtZero : ∀ tools feedback →
    step (ready (budget zero tools) feedback) tick ≡ log modelLimit (finish modelExhausted)
  noModelAtZero tools feedback = refl

  noToolAtZero : ∀ models request →
    step (modelPending (budget models zero)) (modelReply (useTool request)) ≡
    log toolLimit (finish toolExhausted)
  noToolAtZero models request = refl

  lostCommitReadFirst : ∀ fuel arguments →
    step (after (toolPending fuel (call review arguments)) (toolReply lost ∷ [])) traceWritten ≡
    next (receiptPending fuel afterLoss) (readSelectedRevision ∷ [])
  lostCommitReadFirst fuel arguments = refl

  -- A trace failure cannot silently proceed with the pending external action.
  failedTraceStops : ∀ event continuation →
    step (tracing event continuation) traceWriteFailed ≡ next (finished traceFailed) []
  failedTraceStops event continuation = refl

  queuedCallPreservesProviderBudget : ∀ models tools feedback request →
    step (ready (budget models (suc tools)) feedback) (queuedTool request) ≡
    log toolRequested (invoke (budget models tools) request)
  queuedCallPreservesProviderBudget models tools feedback request = refl

  queuedMalformedPreservesProviderBudget : ∀ models tools feedback failure →
    step (ready (budget models (suc tools)) feedback) (queuedMalformed failure) ≡
    log (inputRejected failure) (reconsider (budget models tools) (rejected failure))
  queuedMalformedPreservesProviderBudget models tools feedback failure = refl

  unclassifiedReviewRequiresReceipt : ∀ fuel arguments failure →
    step (toolPending fuel (call review arguments)) (toolReply (indeterminate failure)) ≡
    log (unclassifiedFailure failure) (observe fuel (afterIndeterminate failure))
  unclassifiedReviewRequiresReceipt fuel arguments failure = refl

  pendingUnclassifiedFailureRetainsCause : ∀ fuel failure →
    pendingReceipt fuel (afterIndeterminate failure) ≡
    log receiptPending (reconsider fuel (indeterminateFailure failure))
  pendingUnclassifiedFailureRetainsCause fuel failure = refl
