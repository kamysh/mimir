{-# OPTIONS --safe #-}
-- Wire error data reaches the existing judge controller. The continuation
-- theorem explicitly includes the trace acknowledgements that precede a
-- subsequent model request; decoding an error cannot invent those receipts.
import Mimir.FloatConversion
module Mimir.McpErrorDelivery (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Integer using (ℤ)
open import Data.Nat using (suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Mimir.ReviewObservation using (Pin)
import Mimir.StructuredValue as V
import Mimir.McpErrors as Errors
import Mimir.McpErrorWire as WireDependency
private
  module Wire = WireDependency floatConversion
import Mimir.JudgeErrorAdapter as Adapter
import Mimir.JudgeReview as Review

module Delivery (Payload : Set) (selected : Pin) (minimum maximum expectedCode : ℤ) where
  module W = Wire.BoundedCodes minimum maximum
  module A = Adapter.Adapter Payload selected
  module C = Review.Controller Payload selected

  dispatch : V.Value → A.Dispatch
  dispatch raw = A.route (Errors.classifyAt expectedCode (W.decode raw))

  encodedRefusal : Errors.Refusal → V.Value
  encodedRefusal report = W.encode (Errors.encodeAt expectedCode report)

  validationExact : ∀ failure → W.InRange expectedCode →
    dispatch (encodedRefusal (Errors.refusal Errors.invalidInput failure)) ≡ A.ordinary (C.refused failure)
  validationExact failure bounded = cong A.route
    (W.structuredRefusalPreserved expectedCode (Errors.refusal Errors.invalidInput failure) bounded)

  candidateConflictDistinct : ∀ failure → W.InRange expectedCode →
    dispatch (encodedRefusal (Errors.refusal Errors.candidateConflict failure)) ≡ A.candidateConflict failure
  candidateConflictDistinct failure bounded = cong A.route
    (W.structuredRefusalPreserved expectedCode (Errors.refusal Errors.candidateConflict failure) bounded)

  candidateReferenceDistinct : ∀ failure → W.InRange expectedCode →
    dispatch (encodedRefusal (Errors.refusal Errors.undeclaredCandidate failure)) ≡ A.candidateReference failure
  candidateReferenceDistinct failure bounded = cong A.route
    (W.structuredRefusalPreserved expectedCode (Errors.refusal Errors.undeclaredCandidate failure) bounded)

  legacyIndeterminate : ∀ code message → W.InRange code →
    dispatch (W.encode (Errors.error code message nothing)) ≡
    A.ordinary (C.indeterminate (Errors.error code message nothing))
  legacyIndeterminate code message bounded = cong A.route (W.legacyRemainsUnclassified expectedCode code message bounded)

  ordinaryInput : A.Dispatch → Maybe C.Input
  ordinaryInput (A.ordinary reply) = just (C.toolReply reply)
  ordinaryInput (A.candidateConflict failure) = nothing
  ordinaryInput (A.candidateReference failure) = nothing

  -- A caller must supply the actual sequence, including persisted-log
  -- acknowledgements. Candidate retries belong to their separate controller.
  continue : C.State → List C.Input → C.Input → Maybe C.Input → Maybe C.Step
  continue state intervening final nothing = nothing
  continue state intervening final (just first) = just
    (C.step (C.after state (first ∷ intervening)) final)

  wireRejectionDelivered : ∀ models tools request failure → W.InRange expectedCode →
    continue (C.toolPending (C.budget (suc models) tools) request) (C.traceWritten ∷ C.tick ∷ []) C.traceWritten
      (ordinaryInput (dispatch (encodedRefusal (Errors.refusal Errors.invalidInput failure)))) ≡
    just (C.next (C.modelPending (C.budget models tools)) (C.requestModel (C.rejected failure) ∷ []))
  wireRejectionDelivered models tools request failure bounded =
    trans (cong (λ routed → continue (C.toolPending (C.budget (suc models) tools) request) (C.traceWritten ∷ C.tick ∷ []) C.traceWritten
      (ordinaryInput routed)) (validationExact failure bounded))
      (cong just (C.rejectionDelivered models tools request failure))
