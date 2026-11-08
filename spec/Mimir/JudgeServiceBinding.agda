{-# OPTIONS --safe #-}
-- The judge's scoped tools use the same public MCP operation as other clients.
-- A successful local service receipt requires both the client request trace
-- and the actual application's execution with that exact argument/result.
module Mimir.JudgeServiceBinding where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Integer using (-[1+_])
import Data.Integer.Properties as Integer
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _≤_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (toList)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
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
import Mimir.StructuredValue as V
import Mimir.Validation as Validation
import Mimir.McpErrors as Errors
import Mimir.ApplicationStore as Store
module Correction = Errors.AgentCorrection
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
  module H = Handler.Run environment format conversion
  module A = Application.Run environment

  applicationCode : V.Value → Bool
  applicationCode (V.signed n) = does (n Integer.≟ -[1+ 31999 ])
  applicationCode _ = false

  conflict : V.Value → Bool
  conflict value with Scope.get "message" value
  ... | V.string message = applicationCode (Scope.get "code" value) ∧
      Display.contains errors message (toList "candidate key has a different declaration")
  ... | _ = false

  application : Catalog.Tool → V.Value → Scope.Failure
  application Catalog.reviewExperience value with conflict value
  ... | true = Scope.candidateConflict (toList "review candidate key conflicts with an earlier declaration")
  ... | false with Scope.textIs (toList "candidate belief reference must be declared in this review") (Scope.get "message" value) ∧
      applicationCode (Scope.get "code" value)
  ...   | true = Scope.transport (toList "candidate belief reference is not declared in this review")
  ...   | false = Scope.application (Display.applicationFailure errors value)
  application _ value = Scope.application (Display.applicationFailure errors value)

  toolResult : W.ToolResult → Scope.Failure ⊎ V.Value
  toolResult (W.applicationFailure value) = inj₁ (Scope.application (toList "MCP tool returned isError"))
  toolResult (W.invalidEnvelope failure) = inj₁ (Scope.invalidResponse (Validation.Fault.explanation failure))
  toolResult (W.invalidJSON source failure) with J.text (toList "invalid MCP tool JSON") source
  ... | inj₁ captured with Revision.Error.source captured
  ...   | just source = inj₁ (Scope.sourceFailure source)
  ...   | nothing = inj₁ (Scope.invalidResponse (Revision.Error.detail captured))
  toolResult (W.invalidJSON source failure) | inj₂ value = inj₁ (Scope.invalidResponse (Validation.Fault.explanation failure))
  toolResult (W.toolValue source value) = inj₂ value

  decode : Catalog.Tool → C.Outcome → Scope.Failure ⊎ V.Value
  decode tool (C.transportFailure failure) = inj₁ (Scope.transport (Validation.Fault.explanation failure))
  decode tool (C.syntaxFailure failure) = inj₁ (Scope.invalidResponse (Validation.Fault.explanation failure))
  decode tool (C.protocolFailure failure) = inj₁ (Scope.invalidResponse (Display.protocolFailure errors failure))
  decode tool (C.applicationFailure value) = inj₁ (application tool value)
  decode tool (C.success value) = toolResult (W.tool value)

  params : Catalog.Tool → V.Value → V.Value
  params tool args = Encoding.object (("name" , V.string (toList (Catalog.wireName tool))) ∷ ("arguments" , args) ∷ [])

  data ClientCall (id : ℕ) (tool : Catalog.Tool) (args : V.Value) : Scope.Failure ⊎ V.Value → Set where
    clientCall : ∀ diagnostics outcome events reply →
      T.With.Pending.Runs diagnostics id (T.With.Pending.start diagnostics id (toList "tools/call") (params tool args)) events outcome →
      decode tool outcome ≡ reply → ClientCall id tool args reply
    counterFull : 18446744073709551615 ≤ id →
      ClientCall id tool args (inj₁ (Scope.transport (toList "MCP request ID overflow")))

  -- Successful replies cannot originate solely from a transport transcript.
  -- They additionally identify the application operation that produced them.
  data Publication (tool : Catalog.Tool) (args : V.Value) : Scope.Failure ⊎ V.Value → Set where
    failed : ∀ failure → Publication tool args (inj₁ failure)
    succeeded : ∀ events value → H.Handled (Envelope.literal (Catalog.wireName tool)) args events (H.completed value) →
      Publication tool args (inj₂ value)

  -- Ordinary tool transport also carries admission dialogue. It is not a
  -- completed publication, and its handler has no application events.
  data Dialogue (tool : Catalog.Tool) (args : V.Value) : Scope.Failure ⊎ V.Value → Set where
    corrected : ∀ {before after} (proof : Correction.Certified Store.World before after) →
      H.Handled (Envelope.literal (Catalog.wireName tool)) args []
        (H.inputCorrection (Correction.Certified.report proof)) →
      Dialogue tool args (inj₂ (Correction.emitCorrection proof))
    preparation : ∀ {before after : Store.World} events
      (proof : Correction.Certified Store.BusinessSnapshot
        (Store.businessSnapshot before) (Store.businessSnapshot after)) →
      H.Handled (Envelope.literal (Catalog.wireName tool)) args events
        (H.preparationDecision (Correction.Certified.report proof)) →
      Dialogue tool args (inj₂ (Correction.emitCorrection proof))

  record Receipt (id : ℕ) (tool : Catalog.Tool) (args : V.Value) (reply : Scope.Failure ⊎ V.Value) : Set where
    field client : ClientCall id tool args reply
          publication : Publication tool args reply ⊎ Dialogue tool args reply

  issued : ∀ {id tool args reply} → Receipt id tool args reply → Client.Issued
  issued {id} receipt with Receipt.client receipt
  ... | clientCall diagnostics outcome events reply execution decoded = Client.issued id
  ... | counterFull bounded = Client.overflowRejected id

  successRequiresExecution : ∀ tool args value → Publication tool args (inj₂ value) →
    Data.Product.Σ (List A.Event) (λ events → H.Operation (Envelope.literal (Catalog.wireName tool)) args events value)
  successRequiresExecution tool args value (succeeded events .value handled) =
    events , H.successRequiresOperation (Envelope.literal (Catalog.wireName tool)) args events value handled
