{-# OPTIONS --safe #-}
-- Every external request is the continuation of an acknowledged trace write.
-- This covers all inputs, including unsolicited and late replies, rather than
-- only a selected happy-path sequence.
module Mimir.JudgeTraceBarrier where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (zero; suc)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.ReviewObservation using (Pin)
import Mimir.JudgeReview as Review

module Barrier (Payload : Set) (selected : Pin) where
  module C = Review.Controller Payload selected

  Permission : C.State → C.Input → C.Effect → Set
  Permission state input (C.persist event) = ⊤
  Permission state input C.cancelOwnedRequests = ⊤
  Permission state input (C.requestModel feedback) =
    Σ C.Trace λ event → Σ C.Budget λ fuel →
      state ≡ C.tracing event (C.ask fuel feedback) × input ≡ C.traceWritten
  Permission state input (C.requestTool request) =
    Σ C.Trace λ event → Σ C.Budget λ fuel →
      state ≡ C.tracing event (C.invoke fuel request) × input ≡ C.traceWritten
  Permission state input C.readSelectedRevision =
    Σ C.Trace λ event → Σ C.Budget λ fuel → Σ C.Purpose λ purpose →
      state ≡ C.tracing event (C.observe fuel purpose) × input ≡ C.traceWritten

  resumePermission : ∀ event continuation →
    All (Permission (C.tracing event continuation) C.traceWritten) (C.Step.effects (C.resume continuation))
  resumePermission event (C.ask fuel feedback) = (event , fuel , refl , refl) ∷ []
  resumePermission event (C.invoke fuel request) = (event , fuel , refl , refl) ∷ []
  resumePermission event (C.observe fuel purpose) = (event , fuel , purpose , refl , refl) ∷ []
  resumePermission event (C.reconsider fuel feedback) = []
  resumePermission event (C.finish result) = []

  pendingPermission : ∀ state input fuel purpose →
    All (Permission state input) (C.Step.effects (C.pendingReceipt fuel purpose))
  pendingPermission state input fuel C.afterReview = tt ∷ []
  pendingPermission state input fuel C.afterLoss = tt ∷ []
  pendingPermission state input fuel C.afterDone = tt ∷ []
  pendingPermission state input fuel (C.afterIndeterminate faultValue) = tt ∷ []

  logs : List C.Effect → List C.Trace
  logs [] = []
  logs (C.persist event ∷ rest) = event ∷ logs rest
  logs (C.requestModel feedback ∷ rest) = logs rest
  logs (C.requestTool request ∷ rest) = logs rest
  logs (C.readSelectedRevision ∷ rest) = logs rest
  logs (C.cancelOwnedRequests ∷ rest) = logs rest

  Supported : C.State → List C.Trace → Set
  Supported (C.tracing event continuation) history = event ∈ history
  Supported state history = ⊤

  resumeSupported : ∀ continuation history → Supported (C.Step.state (C.resume continuation)) history
  resumeSupported (C.ask fuel feedback) history = tt
  resumeSupported (C.invoke fuel request) history = tt
  resumeSupported (C.observe fuel purpose) history = tt
  resumeSupported (C.reconsider fuel feedback) history = tt
  resumeSupported (C.finish result) history = tt

  pendingSupported : ∀ fuel purpose history →
    Supported (C.Step.state (C.pendingReceipt fuel purpose))
      (logs (C.Step.effects (C.pendingReceipt fuel purpose)) ++ history)
  pendingSupported fuel C.afterReview history = here refl
  pendingSupported fuel C.afterLoss history = here refl
  pendingSupported fuel C.afterDone history = here refl
  pendingSupported fuel (C.afterIndeterminate faultValue) history = here refl

  requestsLogged : ∀ state input →
    All (Permission state input) (C.Step.effects (C.step state input))
  requestsLogged state C.stop = tt ∷ []
  requestsLogged (C.ready (C.budget zero tools) feedback) C.tick = tt ∷ []
  requestsLogged (C.ready (C.budget (suc models) tools) feedback) C.tick = tt ∷ []
  requestsLogged (C.tracing event continuation) C.tick = []
  requestsLogged (C.modelPending actual) C.tick = []
  requestsLogged (C.toolPending actual request) C.tick = []
  requestsLogged (C.receiptPending actual purpose) C.tick = []
  requestsLogged (C.finished result) C.tick = []
  requestsLogged (C.tracing event continuation) C.traceWritten = resumePermission event continuation
  requestsLogged (C.ready actual feedback) C.traceWritten = []
  requestsLogged (C.modelPending actual) C.traceWritten = []
  requestsLogged (C.toolPending actual request) C.traceWritten = []
  requestsLogged (C.receiptPending actual purpose) C.traceWritten = []
  requestsLogged (C.finished result) C.traceWritten = []
  requestsLogged (C.tracing event continuation) C.traceWriteFailed = []
  requestsLogged (C.ready actual feedback) C.traceWriteFailed = []
  requestsLogged (C.modelPending actual) C.traceWriteFailed = []
  requestsLogged (C.toolPending actual request) C.traceWriteFailed = []
  requestsLogged (C.receiptPending actual purpose) C.traceWriteFailed = []
  requestsLogged (C.finished result) C.traceWriteFailed = []
  requestsLogged (C.ready actual feedback) C.timeout = []
  requestsLogged (C.tracing event continuation) C.timeout = []
  requestsLogged (C.modelPending actual) C.timeout = tt ∷ []
  requestsLogged (C.toolPending actual (C.call (C.query operation) arguments)) C.timeout = tt ∷ []
  requestsLogged (C.toolPending actual (C.call C.review arguments)) C.timeout = tt ∷ []
  requestsLogged (C.receiptPending actual purpose) C.timeout = tt ∷ []
  requestsLogged (C.finished result) C.timeout = []
  requestsLogged (C.modelPending actual) (C.modelReply C.done) = tt ∷ []
  requestsLogged (C.modelPending (C.budget models zero)) (C.modelReply (C.useTool request)) = tt ∷ []
  requestsLogged (C.modelPending (C.budget models (suc tools))) (C.modelReply (C.useTool request)) = tt ∷ []
  requestsLogged (C.modelPending (C.budget models zero)) (C.modelReply (C.malformed faultValue)) = tt ∷ []
  requestsLogged (C.modelPending (C.budget models (suc tools))) (C.modelReply (C.malformed faultValue)) = tt ∷ []
  requestsLogged (C.ready actual feedback) (C.modelReply action) = []
  requestsLogged (C.tracing event continuation) (C.modelReply action) = []
  requestsLogged (C.toolPending actual request) (C.modelReply action) = []
  requestsLogged (C.receiptPending actual purpose) (C.modelReply action) = []
  requestsLogged (C.finished result) (C.modelReply action) = []
  requestsLogged (C.ready (C.budget models zero) feedback) (C.queuedTool request) = tt ∷ []
  requestsLogged (C.ready (C.budget models (suc tools)) feedback) (C.queuedTool request) = tt ∷ []
  requestsLogged (C.tracing event continuation) (C.queuedTool request) = []
  requestsLogged (C.modelPending actual) (C.queuedTool request) = []
  requestsLogged (C.toolPending actual current) (C.queuedTool request) = []
  requestsLogged (C.receiptPending actual purpose) (C.queuedTool request) = []
  requestsLogged (C.finished result) (C.queuedTool request) = []
  requestsLogged (C.ready (C.budget models zero) feedback) (C.queuedMalformed faultValue) = tt ∷ []
  requestsLogged (C.ready (C.budget models (suc tools)) feedback) (C.queuedMalformed faultValue) = tt ∷ []
  requestsLogged (C.tracing event continuation) (C.queuedMalformed faultValue) = []
  requestsLogged (C.modelPending actual) (C.queuedMalformed faultValue) = []
  requestsLogged (C.toolPending actual current) (C.queuedMalformed faultValue) = []
  requestsLogged (C.receiptPending actual purpose) (C.queuedMalformed faultValue) = []
  requestsLogged (C.finished result) (C.queuedMalformed faultValue) = []
  requestsLogged (C.toolPending actual (C.call (C.query operation) arguments)) (C.toolReply (C.returned value)) = tt ∷ []
  requestsLogged (C.toolPending actual (C.call C.review arguments)) (C.toolReply (C.returned value)) = tt ∷ []
  requestsLogged (C.toolPending actual (C.call (C.query operation) arguments)) (C.toolReply (C.refused faultValue)) = tt ∷ []
  requestsLogged (C.toolPending actual (C.call C.review arguments)) (C.toolReply (C.refused faultValue)) = tt ∷ []
  requestsLogged (C.toolPending actual (C.call (C.query operation) arguments)) (C.toolReply C.lost) = tt ∷ []
  requestsLogged (C.toolPending actual (C.call C.review arguments)) (C.toolReply C.lost) = tt ∷ []
  requestsLogged (C.toolPending actual (C.call (C.query operation) arguments)) (C.toolReply (C.indeterminate faultValue)) = tt ∷ []
  requestsLogged (C.toolPending actual (C.call C.review arguments)) (C.toolReply (C.indeterminate faultValue)) = tt ∷ []
  requestsLogged (C.ready actual feedback) (C.toolReply reply) = []
  requestsLogged (C.tracing event continuation) (C.toolReply reply) = []
  requestsLogged (C.modelPending actual) (C.toolReply reply) = []
  requestsLogged (C.receiptPending actual purpose) (C.toolReply reply) = []
  requestsLogged (C.finished result) (C.toolReply reply) = []
  requestsLogged (C.receiptPending actual purpose) (C.receipt (C.acknowledged receiptEvidence)) = tt ∷ []
  requestsLogged (C.receiptPending actual purpose) (C.receipt C.changed) = tt ∷ []
  requestsLogged (C.receiptPending actual purpose) (C.receipt C.pending) = pendingPermission (C.receiptPending actual purpose) (C.receipt C.pending) actual purpose
  requestsLogged (C.receiptPending actual purpose) (C.receipt C.unavailable) = tt ∷ []
  requestsLogged (C.ready actual feedback) (C.receipt reply) = []
  requestsLogged (C.tracing event continuation) (C.receipt reply) = []
  requestsLogged (C.modelPending actual) (C.receipt reply) = []
  requestsLogged (C.toolPending actual request) (C.receipt reply) = []
  requestsLogged (C.finished result) (C.receipt reply) = []

  supportsNext : ∀ state input history → Supported state history →
    Supported (C.Step.state (C.step state input)) (logs (C.Step.effects (C.step state input)) ++ history)
  supportsNext state C.stop history supported = tt
  supportsNext (C.ready (C.budget zero tools) feedback) C.tick history supported = here refl
  supportsNext (C.ready (C.budget (suc models) tools) feedback) C.tick history supported = here refl
  supportsNext (C.tracing event continuation) C.tick history supported = supported
  supportsNext (C.modelPending actual) C.tick history supported = tt
  supportsNext (C.toolPending actual request) C.tick history supported = tt
  supportsNext (C.receiptPending actual purpose) C.tick history supported = tt
  supportsNext (C.finished result) C.tick history supported = tt
  supportsNext (C.tracing event continuation) C.traceWritten history supported =
    resumeSupported continuation (logs (C.Step.effects (C.resume continuation)) ++ history)
  supportsNext (C.ready actual feedback) C.traceWritten history supported = tt
  supportsNext (C.modelPending actual) C.traceWritten history supported = tt
  supportsNext (C.toolPending actual request) C.traceWritten history supported = tt
  supportsNext (C.receiptPending actual purpose) C.traceWritten history supported = tt
  supportsNext (C.finished result) C.traceWritten history supported = tt
  supportsNext (C.tracing event continuation) C.traceWriteFailed history supported = tt
  supportsNext (C.ready actual feedback) C.traceWriteFailed history supported = tt
  supportsNext (C.modelPending actual) C.traceWriteFailed history supported = tt
  supportsNext (C.toolPending actual request) C.traceWriteFailed history supported = tt
  supportsNext (C.receiptPending actual purpose) C.traceWriteFailed history supported = tt
  supportsNext (C.finished result) C.traceWriteFailed history supported = tt
  supportsNext (C.ready actual feedback) C.timeout history supported = tt
  supportsNext (C.tracing event continuation) C.timeout history supported = tt
  supportsNext (C.modelPending actual) C.timeout history supported = here refl
  supportsNext (C.toolPending actual (C.call (C.query operation) arguments)) C.timeout history supported = here refl
  supportsNext (C.toolPending actual (C.call C.review arguments)) C.timeout history supported = here refl
  supportsNext (C.receiptPending actual purpose) C.timeout history supported = here refl
  supportsNext (C.finished result) C.timeout history supported = tt
  supportsNext (C.modelPending actual) (C.modelReply C.done) history supported = here refl
  supportsNext (C.modelPending (C.budget models zero)) (C.modelReply (C.useTool request)) history supported = here refl
  supportsNext (C.modelPending (C.budget models (suc tools))) (C.modelReply (C.useTool request)) history supported = here refl
  supportsNext (C.modelPending (C.budget models zero)) (C.modelReply (C.malformed faultValue)) history supported = here refl
  supportsNext (C.modelPending (C.budget models (suc tools))) (C.modelReply (C.malformed faultValue)) history supported = here refl
  supportsNext (C.ready actual feedback) (C.modelReply action) history supported = tt
  supportsNext (C.tracing event continuation) (C.modelReply action) history supported = supported
  supportsNext (C.toolPending actual request) (C.modelReply action) history supported = tt
  supportsNext (C.receiptPending actual purpose) (C.modelReply action) history supported = tt
  supportsNext (C.finished result) (C.modelReply action) history supported = tt
  supportsNext (C.ready (C.budget models zero) feedback) (C.queuedTool request) history supported = here refl
  supportsNext (C.ready (C.budget models (suc tools)) feedback) (C.queuedTool request) history supported = here refl
  supportsNext (C.tracing event continuation) (C.queuedTool request) history supported = supported
  supportsNext (C.modelPending actual) (C.queuedTool request) history supported = tt
  supportsNext (C.toolPending actual current) (C.queuedTool request) history supported = tt
  supportsNext (C.receiptPending actual purpose) (C.queuedTool request) history supported = tt
  supportsNext (C.finished result) (C.queuedTool request) history supported = tt
  supportsNext (C.ready (C.budget models zero) feedback) (C.queuedMalformed faultValue) history supported = here refl
  supportsNext (C.ready (C.budget models (suc tools)) feedback) (C.queuedMalformed faultValue) history supported = here refl
  supportsNext (C.tracing event continuation) (C.queuedMalformed faultValue) history supported = supported
  supportsNext (C.modelPending actual) (C.queuedMalformed faultValue) history supported = tt
  supportsNext (C.toolPending actual current) (C.queuedMalformed faultValue) history supported = tt
  supportsNext (C.receiptPending actual purpose) (C.queuedMalformed faultValue) history supported = tt
  supportsNext (C.finished result) (C.queuedMalformed faultValue) history supported = tt
  supportsNext (C.toolPending actual (C.call (C.query operation) arguments)) (C.toolReply (C.returned value)) history supported = here refl
  supportsNext (C.toolPending actual (C.call C.review arguments)) (C.toolReply (C.returned value)) history supported = here refl
  supportsNext (C.toolPending actual (C.call (C.query operation) arguments)) (C.toolReply (C.refused faultValue)) history supported = here refl
  supportsNext (C.toolPending actual (C.call C.review arguments)) (C.toolReply (C.refused faultValue)) history supported = here refl
  supportsNext (C.toolPending actual (C.call (C.query operation) arguments)) (C.toolReply C.lost) history supported = here refl
  supportsNext (C.toolPending actual (C.call C.review arguments)) (C.toolReply C.lost) history supported = here refl
  supportsNext (C.toolPending actual (C.call (C.query operation) arguments)) (C.toolReply (C.indeterminate faultValue)) history supported = here refl
  supportsNext (C.toolPending actual (C.call C.review arguments)) (C.toolReply (C.indeterminate faultValue)) history supported = here refl
  supportsNext (C.ready actual feedback) (C.toolReply reply) history supported = tt
  supportsNext (C.tracing event continuation) (C.toolReply reply) history supported = supported
  supportsNext (C.modelPending actual) (C.toolReply reply) history supported = tt
  supportsNext (C.receiptPending actual purpose) (C.toolReply reply) history supported = tt
  supportsNext (C.finished result) (C.toolReply reply) history supported = tt
  supportsNext (C.receiptPending actual purpose) (C.receipt (C.acknowledged receiptEvidence)) history supported = here refl
  supportsNext (C.receiptPending actual purpose) (C.receipt C.changed) history supported = here refl
  supportsNext (C.receiptPending actual purpose) (C.receipt C.pending) history supported = pendingSupported actual purpose history
  supportsNext (C.receiptPending actual purpose) (C.receipt C.unavailable) history supported = here refl
  supportsNext (C.ready actual feedback) (C.receipt reply) history supported = tt
  supportsNext (C.tracing event continuation) (C.receipt reply) history supported = supported
  supportsNext (C.modelPending actual) (C.receipt reply) history supported = tt
  supportsNext (C.toolPending actual request) (C.receipt reply) history supported = tt
  supportsNext (C.finished result) (C.receipt reply) history supported = tt

  Origin : List C.Trace → C.Effect → Set
  Origin history (C.persist event) = ⊤
  Origin history C.cancelOwnedRequests = ⊤
  Origin history (C.requestModel feedback) = Σ C.Trace (λ event → event ∈ history)
  Origin history (C.requestTool request) = Σ C.Trace (λ event → event ∈ history)
  Origin history C.readSelectedRevision = Σ C.Trace (λ event → event ∈ history)

  permissionHasOrigin : ∀ state input history → Supported state history →
    ∀ effect → Permission state input effect → Origin history effect
  permissionHasOrigin state input history supported (C.persist event) permission = tt
  permissionHasOrigin state input history supported C.cancelOwnedRequests permission = tt
  permissionHasOrigin .(C.tracing event (C.ask fuel feedback)) .C.traceWritten history supported
    (C.requestModel feedback) (event , fuel , refl , refl) = event , supported
  permissionHasOrigin .(C.tracing event (C.invoke fuel request)) .C.traceWritten history supported
    (C.requestTool request) (event , fuel , refl , refl) = event , supported
  permissionHasOrigin .(C.tracing event (C.observe fuel purpose)) .C.traceWritten history supported
    C.readSelectedRevision (event , fuel , purpose , refl , refl) = event , supported

  stepCertified : ∀ state input history → Supported state history →
    All (λ effect → Permission state input effect × Origin history effect)
      (C.Step.effects (C.step state input))
  stepCertified state input history supported = certify (requestsLogged state input)
    where
    certify : ∀ {effects} → All (Permission state input) effects →
      All (λ effect → Permission state input effect × Origin history effect) effects
    certify [] = []
    certify {effect ∷ rest} (permission ∷ permissions) =
      (permission , permissionHasOrigin state input history supported effect permission) ∷ certify permissions

  data Certified : C.State → List C.Trace → List C.Input → Set where
    empty : ∀ {state history} → Certified state history []
    more : ∀ {state history input rest} →
      All (λ effect → Permission state input effect × Origin history effect)
        (C.Step.effects (C.step state input)) →
      Certified (C.Step.state (C.step state input)) (logs (C.Step.effects (C.step state input)) ++ history) rest →
      Certified state history (input ∷ rest)

  certifyRun : ∀ state history inputs → Supported state history → Certified state history inputs
  certifyRun state history [] supported = empty
  certifyRun state history (input ∷ rest) supported = more (stepCertified state input history supported)
    (certifyRun (C.Step.state (C.step state input)) (logs (C.Step.effects (C.step state input)) ++ history)
      rest (supportsNext state input history supported))

  everyInitialRunCertified : ∀ fuel feedback inputs → Certified (C.ready fuel feedback) [] inputs
  everyInitialRunCertified fuel feedback inputs = certifyRun (C.ready fuel feedback) [] inputs tt
