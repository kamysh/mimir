{-# OPTIONS --safe #-}
-- One owned MCP client's ordered initialization/catalogue/capability exchange.
-- All requests advance its counter; the initialized
-- notification has no ID and consumes no counter value.
module Mimir.JudgeHandshakeBinding where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Mimir.Text using (Text)
import Mimir.FloatConversion as Conversion
import Mimir.JudgeHandshake as H
import Mimir.JudgeMcpLifecycle as Client
import Mimir.McpClientRequest as Request
import Mimir.McpClientTransport as Transport
import Mimir.McpClientWire as Wire
import Mimir.PublicEncoding as Encoding
import Mimir.StructuredValue as V
import Mimir.Validation as Validation
import Mimir.ASCIIPath as ASCII

initializeArgs : V.Value
initializeArgs = Encoding.object
  (("protocolVersion" , V.string (toList "2024-11-05")) ∷
   ("capabilities" , V.object []) ∷
   ("clientInfo" , Encoding.object (("name" , V.string (toList "mimir-judge")) ∷
     ("version" , V.string (toList "1")) ∷ [])) ∷ [])

capabilityArgs : V.Value
capabilityArgs = Encoding.object (("name" , V.string (toList "learning_capabilities")) ∷
  ("arguments" , V.object []) ∷ [])

module Bound (conversion : Conversion.Contract) (diagnostics : Transport.Diagnostics conversion)
  (contract model : ℕ) where
  module C = Client.Calls conversion diagnostics
  module T = Transport conversion
  module R = Request conversion
  module W = Wire conversion
  module Contract = H.Contract contract model

  decode : C.Outcome → Validation.Fault ⊎ V.Value
  decode C.overflow = inj₁ (Validation.fault [] Validation.invalidNumber "MCP request ID overflow")
  decode (C.response (R.transportFailure fault)) = inj₁ fault
  decode (C.response (R.syntaxFailure fault)) = inj₁ fault
  decode (C.response (R.protocolFailure _)) = inj₁ (Validation.fault [] Validation.malformedInput "invalid MCP response")
  decode (C.response (R.applicationFailure _)) = inj₁ (Validation.fault [] Validation.unsupportedCombination "MCP initialization failed")
  decode (C.response (R.success value)) = inj₂ value

  capabilities : C.Outcome → Validation.Fault ⊎ V.Value
  capabilities reply with decode reply
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ value with W.tool value
  ...   | W.toolValue source decoded = inj₂ decoded
  ...   | W.applicationFailure _ = inj₁ (Validation.fault [] Validation.unsupportedCombination "MCP tool returned isError")
  ...   | W.invalidEnvelope fault = inj₁ fault
  ...   | W.invalidJSON _ fault = inj₁ fault

  data Receipt (before : Client.Client) : (effect : H.Effect) → H.Reply effect → Client.Client → Set where
    initialized : ∀ events after result → C.Call before (toList "initialize") initializeArgs events after result →
      Receipt before H.initialize (decode result) after
    notified : ∀ events result → T.E.Runs (T.With.sendBody diagnostics
      (ASCII.literal (toList "{\"jsonrpc\":\"2.0\",\"method\":\"notifications/initialized\",\"params\":{}}") tt)) events result →
      Receipt before H.initializedNotification result before
    tools : ∀ events after result → C.Call before (toList "tools/list") (V.object []) events after result →
      Receipt before H.listTools (decode result) after
    learning : ∀ events after result → C.Call before (toList "tools/call") capabilityArgs events after result →
      Receipt before H.learningCapabilities (capabilities result) after

  data Runs : Client.Client → H.E.Script Contract.Result → List H.E.Event → Client.Client → Contract.Result → Set where
    returned : ∀ client result → Runs client (H.E.done result) [] client result
    replied : ∀ before effect next reply middle events after result → Receipt before effect reply middle →
      Runs middle (next reply) events after result →
      Runs before (H.E.ask effect next) ((effect , reply) ∷ events) after result
