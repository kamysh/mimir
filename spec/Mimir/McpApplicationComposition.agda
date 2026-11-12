{-# OPTIONS --safe #-}
-- Server transport composed with the concrete application handler. Ordinary
-- exchange traces alone allowed arbitrary handleTool replies; this relation
-- requires the actual typed operation trace at every such boundary.
module Mimir.McpApplicationComposition where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.String using (toList)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.McpExchange as Exchange
import Mimir.McpEnvelope as Envelope
import Mimir.McpToolExecution as Handler
import Mimir.StructuredValue as JSON
import Mimir.StructuredValue as Schema
import Mimir.ApplicationProtocol as Application
import Mimir.GraphMutationProtocol as Mutation
import Mimir.BeliefEmbedding as BeliefEmbedding
import Mimir.ApplicationStore as Store
import Mimir.PublicEncoding as Encoding
import Mimir.StandardLibrary as Conversion
import Mimir.Validation as Validation

data External : Exchange.Effect → Set where
  deliver : ∀ response → External (Exchange.deliver response)

module Compose (environment : Application.Environment) (format : Encoding.Formatting)
  (conversion : Conversion.Contract) where
  module H = Handler.Run environment format conversion
    using (Diagnostic; operationFailed; userDecisionRequired; invalidArguments; unknownTool; Result; Handled)
  module A = Application.Run environment using (Result; Event; failed; mutated)

  -- The formatter cannot select application success.
  module WithDiagnostic (render : H.Diagnostic → Text) where
    diagnostic : H.Diagnostic → Text
    diagnostic (H.operationFailed (A.failed detail)) = detail
    diagnostic (H.operationFailed (A.mutated (Mutation.embeddingFailed (BeliefEmbedding.publicationFailed detail)))) =
      detail ++ toList ". No belief was saved. Resolve the reported database problem and retry."
    diagnostic cause = render cause

    decisionRequest : Text → Text → JSON.Value
    decisionRequest reason guidance = Encoding.object
      (("status" , JSON.string (toList "needs_input")) ∷
       ("reason" , JSON.string reason) ∷
       ("next_action" , JSON.string guidance) ∷
       ("interaction" , JSON.string (toList "ask_user")) ∷ [])

    pathSegment : Validation.Segment → JSON.Value
    pathSegment (Validation.fieldKey name) = JSON.string name
    pathSegment (Validation.index index) = JSON.unsigned index

    argumentCorrection : Validation.Fault → JSON.Value
    argumentCorrection fault = Encoding.object
      (("status" , JSON.string (toList "needs_correction")) ∷
       ("path" , JSON.array (map pathSegment (Validation.Fault.path fault))) ∷
       ("reason" , JSON.string (Validation.Fault.explanation fault)) ∷
       ("next_action" , JSON.string (toList "Correct the request using the reason and path, then retry. Consult the tool schema or ask the user if the intended value is unclear.")) ∷ [])

    toolCorrection : Text → JSON.Value
    toolCorrection name = Encoding.object
      (("status" , JSON.string (toList "needs_correction")) ∷
       ("tool" , JSON.string name) ∷
       ("reason" , JSON.string (toList "This tool name is not available.")) ∷
       ("next_action" , JSON.string (toList "List available tools and retry with the intended name. Ask the user if the intent is unclear.")) ∷ [])

    data Materialized : H.Result → Text ⊎ JSON.Value → Set where
      recoveryNeeded : ∀ cause → Materialized (inj₁ (H.operationFailed cause))
        (inj₂ (decisionRequest (diagnostic (H.operationFailed cause))
          (toList "Explain the reported problem and the affected request. Resolve its stated prerequisite or ask the user for the required decision, then retry the original request from the beginning after rollback and cleanup. Do not report the request as completed.")))
      decision : ∀ reason guidance → Materialized (inj₁ (H.userDecisionRequired reason guidance))
        (inj₂ (decisionRequest reason guidance))
      invalid : ∀ fault → Materialized (inj₁ (H.invalidArguments fault)) (inj₂ (argumentCorrection fault))
      unknown : ∀ name → Materialized (inj₁ (H.unknownTool name)) (inj₂ (toolCorrection name))
      value : ∀ schema → Materialized (inj₂ schema) (inj₂ schema)

    decisionIsNotAnError : ∀ reason guidance reply →
      Materialized (inj₁ (H.userDecisionRequired reason guidance)) reply →
      reply ≡ inj₂ (decisionRequest reason guidance)
    decisionIsNotAnError reason guidance ._ (decision .reason .guidance) = refl

    invalidArgumentsAreCorrectable : ∀ fault reply →
      Materialized (inj₁ (H.invalidArguments fault)) reply → reply ≡ inj₂ (argumentCorrection fault)
    invalidArgumentsAreCorrectable fault ._ (invalid .fault) = refl

    diagnosticHasRecoveryReply : ∀ cause → Σ JSON.Value (λ value →
      Materialized (inj₁ cause) (inj₂ value))
    diagnosticHasRecoveryReply (H.operationFailed cause) = _ , recoveryNeeded cause
    diagnosticHasRecoveryReply (H.userDecisionRequired reason guidance) = _ , decision reason guidance
    diagnosticHasRecoveryReply (H.invalidArguments fault) = _ , invalid fault
    diagnosticHasRecoveryReply (H.unknownTool name) = _ , unknown name

    data Event : Set where
      external : (effect : Exchange.Effect) → External effect → Exchange.Reply effect → Event
      tool : Envelope.Identity → Envelope.Text → JSON.Value → List A.Event → Text ⊎ JSON.Value → Event

    outer : Event → Exchange.Event
    outer (external effect permitted reply) = effect , reply
    outer (tool identityValue name args events reply) = Exchange.handleTool identityValue name args , reply

    data Runs : Exchange.Script Exchange.Outcome → Store.World → List Event → Store.World → Exchange.Outcome → Set where
      returned : ∀ result store → Runs (Exchange.done result) store [] store result
      external : ∀ effect permitted continuation reply before events after result →
        Runs (continuation reply) before events after result →
        Runs (Exchange.ask effect continuation) before (external effect permitted reply ∷ events) after result
      tool : ∀ identityValue name args continuation before applicationEvents applicationResult middle reply events after result →
        H.Handled identityValue name args before applicationEvents applicationResult middle →
        Materialized applicationResult reply → Runs (continuation reply) middle events after result →
        Runs (Exchange.ask (Exchange.handleTool identityValue name args) continuation) before
          (tool identityValue name args applicationEvents reply ∷ events) after result

    transportPreserved : ∀ program before events after result → Runs program before events after result →
      Exchange.Runs program (map outer events) result
    transportPreserved program before events after result (returned result₁ store) = Exchange.returned result
    transportPreserved program before events after result (external effect permitted continuation reply .before events₁ .after result₁ proof) =
      Exchange.replied effect continuation reply (transportPreserved (continuation reply) before events₁ after result proof)
    transportPreserved program before events after result (tool identityValue name args continuation .before applicationEvents applicationResult middle reply events₁ .after result₁ handled materialized proof) =
      Exchange.replied (Exchange.handleTool identityValue name args) continuation reply (transportPreserved (continuation reply) middle events₁ after result proof)
