{-# OPTIONS --safe #-}
-- The judge's scoped tools use the same public MCP operation as other clients.
-- A successful local service receipt requires the client request trace and
-- the guarded application execution.
module Mimir.JudgeServiceBinding where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Integer using (-[1+_])
import Data.Integer.Properties as Integer
open import Data.List using (List; []; _∷_; _++_)
open import Data.Nat using (ℕ; _≤_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (toList)
open import Relation.Nullary using (does; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.StandardLibrary as Conversion
import Mimir.PublicEncoding as Encoding
import Mimir.ToolCatalog as Catalog
import Mimir.JudgeScopedTools as Scope
import Mimir.JudgeRevision as Revision
import Mimir.JudgeJSON as JSON
import Mimir.McpClientRequest as Request
import Mimir.McpClientTransport as Transport
import Mimir.McpClientWire as Wire
import Mimir.McpToolExecution as Handler
import Mimir.McpEnvelope as Envelope
import Mimir.ApplicationProtocol as Application
import Mimir.ApplicationStore as Store
import Mimir.StructuredValue as V
import Mimir.Validation as Validation
import Mimir.McpErrors as Errors
import Mimir.SourceFailure as Source
import Mimir.RpcReply
import Mimir.JudgeMcpLifecycle as Client

record Display : Set where
  field requestFailure : Text → Text
        protocolFailure : Mimir.RpcReply.Failure → Text
        applicationFailure : V.Value → Text
        contains : Text → Text → Bool

module Bind (conversion : Conversion.Contract) (format : Encoding.Formatting)
  (display : Revision.Display) (errors : Display) (environment : Application.Environment) where
  module C = Request conversion
  module T = Transport conversion
  module W = Wire conversion
  module J = JSON conversion
  module H = Handler.Run environment format conversion using (Handled; Success; successHasSource)
  module A = Application.Run environment using (Event)

  applicationCode : V.Value → Bool
  applicationCode (V.signed n) = does (n Integer.≟ -[1+ 31999 ])
  applicationCode _ = false

  refusal : Errors.Refusal → Scope.Failure
  refusal (Errors.refusal Errors.invalidInput detail) = Scope.rejected (Revision.Display.fault display detail)
  refusal (Errors.refusal Errors.candidateConflict detail) = Scope.candidateConflict (Revision.Display.fault display detail)
  refusal (Errors.refusal Errors.undeclaredCandidate detail) = Scope.rejected (Revision.Display.fault display detail)

  application : Catalog.Tool → V.Value → Scope.Failure
  application tool value with applicationCode (Scope.get "code" value) | Errors.decodeRefusal (Scope.get "data" value)
  ... | true | inj₂ detail = refusal detail
  ... | _ | _ = Scope.application (Display.applicationFailure errors value)

  fieldPath : V.Value → Text
  fieldPath value with Scope.get "path" value
  ... | V.array path = toList " Field path: " ++ Revision.Display.json display (V.array path) ++ toList "."
  ... | _ = []

  correction : V.Value → Maybe Scope.Failure
  correction value with Scope.get "status" value | Scope.get "reason" value | Scope.get "next_action" value
  ... | V.string status | V.string reason | V.string action with status ≟Text toList "needs_correction"
  ...   | yes _ = just (Scope.rejected (reason ++ fieldPath value ++ toList " " ++ action))
  ...   | no _ with status ≟Text toList "needs_input"
  ...     | yes _ = just (Scope.needsUserDecision (reason ++ toList " " ++ action))
  ...     | no _ = nothing
  correction value | _ | _ | _ = nothing

  toolResult : W.ToolResult → Scope.Failure ⊎ V.Value
  toolResult (W.applicationFailure value) = inj₁ (Scope.application (Display.applicationFailure errors value))
  toolResult (W.invalidEnvelope failure) = inj₁ (Scope.invalidResponse (Validation.Fault.explanation failure))
  toolResult (W.invalidJSON source failure) with J.text (toList "invalid MCP tool JSON") source
  ... | inj₁ captured with Revision.Error.source captured
  ...   | just source = inj₁ (Scope.sourceFailure source)
  ...   | nothing = inj₁ (Scope.invalidResponse (Revision.Error.detail captured))
  toolResult (W.invalidJSON source failure) | inj₂ value = inj₁ (Scope.invalidResponse (Validation.Fault.explanation failure))
  toolResult (W.toolValue source value) with correction value
  ... | just failure = inj₁ failure
  ... | nothing = inj₂ value

  decode : Catalog.Tool → C.Outcome → Scope.Failure ⊎ V.Value
  decode tool (C.transportFailure failure) = inj₁ (Scope.transport (Validation.Fault.explanation failure))
  decode tool (C.syntaxFailure failure) = inj₁ (Scope.invalidResponse (Validation.Fault.explanation failure))
  decode tool (C.protocolFailure failure) = inj₁ (Scope.invalidResponse (Display.protocolFailure errors failure))
  decode tool (C.applicationFailure value) = inj₁ (application tool value)
  decode tool (C.success value) = toolResult (W.tool value)

  params : Catalog.Tool → V.Value → V.Value
  params tool args = Encoding.object (("name" , V.string (toList (Catalog.wireName tool))) ∷ ("arguments" , args) ∷ [])

  data ClientCall (tool : Catalog.Tool) (args : V.Value) : Maybe Text → Scope.Failure ⊎ V.Value → Set where
    clientCall : ∀ id diagnostics outcome allocationEvents events reply →
      Client.Runs (Client.ask Client.randomHexID Client.done) allocationEvents (inj₂ id) →
      T.With.Pending.Runs diagnostics id
        (T.With.Pending.start diagnostics id (toList "tools/call") (params tool args)) events outcome →
      decode tool outcome ≡ reply → ClientCall tool args (just id) reply
    allocationFailed : ∀ events failure →
      Client.Runs (Client.ask Client.randomHexID Client.done) events (inj₁ failure) →
      ClientCall tool args nothing (inj₁ (Scope.transport failure))

  -- Successful replies cannot originate solely from a transport transcript.
  -- They additionally identify the execution that produced them.
  data Publication (tool : Catalog.Tool) (args : V.Value) : Maybe Text → Scope.Failure ⊎ V.Value → Set where
    failed : ∀ id failure → Publication tool args id (inj₁ failure)
    succeeded : ∀ id before after events value → H.Handled (Envelope.identity true (V.string id))
      (Envelope.literal (Catalog.wireName tool)) args before events (inj₂ value) after →
      Publication tool args (just id) (inj₂ value)

  record Receipt (id : Maybe Text) (tool : Catalog.Tool) (args : V.Value) (reply : Scope.Failure ⊎ V.Value) : Set where
    field client : ClientCall tool args id reply
          publication : Publication tool args id reply

  issued : ∀ {id tool args reply} → Receipt id tool args reply → Client.Issued
  issued {id} receipt with Receipt.client receipt
  ... | clientCall allocatedID diagnostics outcome allocationEvents events reply allocated execution decoded = Client.issued allocatedID
  ... | allocationFailed events failure execution = Client.allocationUnavailable

  successHasSource : ∀ id tool args value → Publication tool args (just id) (inj₂ value) →
    Data.Product.Σ Store.World (λ before → Data.Product.Σ Store.World (λ after →
      Data.Product.Σ (List A.Event) (λ events → H.Success (Envelope.identity true (V.string id))
        (Envelope.literal (Catalog.wireName tool)) args before events value after)))
  successHasSource id tool args value (succeeded .id before after events .value handled) =
    before , after , events , H.successHasSource (Envelope.identity true (V.string id))
      (Envelope.literal (Catalog.wireName tool)) args before events value after handled
