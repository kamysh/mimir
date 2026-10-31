{-# OPTIONS --safe #-}
-- Boundary between a provider call queue and selected-review supervision.
-- The provider name determines the operation; an external read/write label
-- cannot turn review_experience into a read-only operation.
module Mimir.JudgeQueueAdapter where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Validation using (Fault)
open import Mimir.ReviewObservation using (Pin)
import Mimir.ProviderQueue as Provider
import Mimir.JudgeTools as Tools
import Mimir.JudgeReview as Review

module Adapter (Payload : Set) (selected : Pin) where
  module Q = Provider.Queue Payload
  module C = Review.Controller Payload selected

  decodeCall : Q.Call → Fault ⊎ C.Call
  decodeCall raw with Q.Call.arguments raw
  ... | inj₁ failure = inj₁ failure
  ... | inj₂ arguments with Tools.decode (Q.Call.name raw)
  ...   | inj₁ failure = inj₁ failure
  ...   | inj₂ kind = inj₂ (C.call kind arguments)

  modelAction : Q.Call → C.ModelAction
  modelAction raw with decodeCall raw
  ... | inj₁ failure = C.malformed failure
  ... | inj₂ request = C.useTool request

  queuedInput : Q.Call → C.Input
  queuedInput raw with decodeCall raw
  ... | inj₁ failure = C.queuedMalformed failure
  ... | inj₂ request = C.queuedTool request

  -- The first call comes from an outstanding provider request. Subsequent
  -- queued calls arrive while ready, after the preceding result was logged.
  input : C.State → Q.Call → C.Input
  input (C.ready fuel feedback) raw = queuedInput raw
  input state raw = C.modelReply (modelAction raw)

  acceptedCallRoundTrip : ∀ identity kind arguments →
    decodeCall (Q.call identity (Tools.name kind) (inj₂ arguments)) ≡ inj₂ (C.call kind arguments)
  acceptedCallRoundTrip identity kind arguments rewrite Tools.everyAllowedNameAccepted kind = refl

  malformedArgumentsPreserved : ∀ identity name failure →
    decodeCall (Q.call identity name (inj₁ failure)) ≡ inj₁ failure
  malformedArgumentsPreserved identity name failure = refl

  namePreserved : ∀ raw request → decodeCall raw ≡ inj₂ request →
    Q.Call.name raw ≡ Tools.name (C.Call.kind request)
  namePreserved raw request success with Q.Call.arguments raw
  ... | inj₁ failure with success
  ...   | ()
  namePreserved raw request success | inj₂ arguments with Tools.decode (Q.Call.name raw) in decoded
  ... | inj₁ failure with success
  ...   | ()
  namePreserved raw request success | inj₂ arguments | inj₂ kind with success
  ... | refl = Tools.decodedNamePreserved (Q.Call.name raw) kind decoded

  argumentsPreserved : ∀ raw request → decodeCall raw ≡ inj₂ request →
    Q.Call.arguments raw ≡ inj₂ (C.Call.arguments request)
  argumentsPreserved raw request success with Q.Call.arguments raw
  ... | inj₁ failure with success
  ...   | ()
  argumentsPreserved raw request success | inj₂ arguments with Tools.decode (Q.Call.name raw)
  ... | inj₁ failure with success
  ...   | ()
  argumentsPreserved raw request success | inj₂ arguments | inj₂ kind with success
  ... | refl = refl

  queuedUsesNoProviderAttempt : ∀ models tools feedback identity kind arguments →
    C.step (C.ready (C.budget models (suc tools)) feedback)
      (input (C.ready (C.budget models (suc tools)) feedback)
        (Q.call identity (Tools.name kind) (inj₂ arguments))) ≡
    C.log C.toolRequested (C.invoke (C.budget models tools) (C.call kind arguments))
  queuedUsesNoProviderAttempt models tools feedback identity kind arguments
    rewrite acceptedCallRoundTrip identity kind arguments = refl
