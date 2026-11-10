{-# OPTIONS --safe #-}
-- Server transport composed with the concrete application handler. Ordinary
-- exchange traces alone allowed arbitrary handleTool replies; this relation
-- requires the actual typed operation trace at every such boundary.
module Mimir.McpApplicationComposition where

open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.McpExchange as Exchange
import Mimir.McpEnvelope as Envelope
import Mimir.McpToolExecution as Handler
import Mimir.StructuredValue as JSON
import Mimir.StructuredValue as Schema
import Mimir.ApplicationProtocol as Application
import Mimir.ApplicationOutput as Output
import Mimir.PublicEncoding as Encoding
import Mimir.StandardLibrary as Conversion
import Mimir.ApplicationStore as Store
import Mimir.McpErrors as Errors
import Mimir.GraphMutationProtocol as Mutation
import Mimir.DatabaseTransaction as Database
import Mimir.ReviewSchema as Review
module Correction = Errors.AgentCorrection

data External : Exchange.Effect → Set where
  format : ∀ value → External (Exchange.formatTool value)
  serialize : ∀ response → External (Exchange.serialize response)
  write : ∀ bytes → External (Exchange.write bytes)
  flush : External Exchange.flush

module Compose (environment : Application.Environment) (format : Encoding.Formatting)
  (conversion : Conversion.Contract) where
  module H = Handler.Run environment format conversion using
    (Diagnostic; Result; failure; completed; inputCorrection; preparationDecision;
     partialDecision; boundReferenceDecision; Handled; module P)
  private
    module A = Application.Run environment using (Result; module Result; Event; reached)
    module Wire = Output.Encode environment format using (boundReferenceValue)

  -- Diagnostic rendering is the approved standard formatter boundary. It
  -- receives the retained typed cause; it cannot select application success.
  module WithDiagnostic (render : H.Diagnostic → Text) where
    data Materialized : H.Result → Text ⊎ JSON.Value → Set where
      error : ∀ cause → Materialized (H.failure cause) (inj₁ (render cause))
      value : ∀ schema → Materialized (H.completed schema) (inj₂ schema)
      correction : ∀ {before after} (proof : Correction.Certified Store.World before after) →
        Materialized (H.inputCorrection (Correction.Certified.report proof)) (inj₂ (Correction.emitCorrection proof))
      preparation : ∀ actual report →
        (unchanged : Store.businessSnapshot (A.reached actual) ≡
          Store.businessSnapshot (A.Result.initial actual)) →
        Materialized (H.preparationDecision actual report)
          (inj₂ (Correction.emitCorrection (Correction.certified report unchanged)))
      partial : ∀ actual edge report →
        Materialized (H.partialDecision actual edge report) (inj₂ (H.P.partialValue edge report))
      boundReference : ∀ actual binding detail →
        Materialized (H.boundReferenceDecision actual binding detail)
          (inj₂ (Wire.boundReferenceValue actual binding detail))

    data Event : Set where
      external : (effect : Exchange.Effect) → External effect → Exchange.Reply effect → Event
      tool : Envelope.Text → JSON.Value → List A.Event → Text ⊎ JSON.Value → Event

    outer : Event → Exchange.Event
    outer (external effect permitted reply) = effect , reply
    outer (tool name args events reply) = Exchange.handleTool name args , reply

    data Runs : Exchange.Script Exchange.Outcome → List Event → Exchange.Outcome → Set where
      returned : ∀ result → Runs (Exchange.done result) [] result
      external : ∀ effect permitted continuation reply events result →
        Runs (continuation reply) events result →
        Runs (Exchange.ask effect continuation) (external effect permitted reply ∷ events) result
      tool : ∀ name args continuation applicationEvents applicationResult reply events result →
        H.Handled name args applicationEvents applicationResult →
        Materialized applicationResult reply → Runs (continuation reply) events result →
        Runs (Exchange.ask (Exchange.handleTool name args) continuation)
          (tool name args applicationEvents reply ∷ events) result

    transportPreserved : ∀ program events result → Runs program events result →
      Exchange.Runs program (map outer events) result
    transportPreserved program events result (returned result₁) = Exchange.returned result
    transportPreserved program events result (external effect permitted continuation reply events₁ result₁ proof) =
      Exchange.replied effect continuation reply (transportPreserved (continuation reply) events₁ result proof)
    transportPreserved program events result (tool name args continuation applicationEvents applicationResult reply events₁ result₁ handled materialized proof) =
      Exchange.replied (Exchange.handleTool name args) continuation reply (transportPreserved (continuation reply) events₁ result proof)
