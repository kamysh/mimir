{-# OPTIONS --safe #-}
-- One server exchange. Envelope admission and notification suppression precede
-- every business handler.
-- Serialization, partial writes and flushes have separate receipts; no write
-- failure is silently retried and a write request is not an acknowledgement.
module Mimir.McpExchange where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (#_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Integer using (ℤ; -[1+_])
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Bits using (Byte)
open import Mimir.Text using (Text)
open import Data.String using (toList; fromList)
import Mimir.StructuredValue as JSON
import Mimir.McpEnvelope as Envelope
import Mimir.Effects as Effects
import Mimir.Validation as V

data Payload : Set where
  initialized tools : Payload
  content : Text → Payload

data Response : Set where
  ok : JSON.Value → Payload → Response
  error : JSON.Value → ℤ → Text → Response
  protocolProblem : Envelope.Problem → Response

data WriteReply (bytes : List Byte) : Set where
  written : WriteReply bytes
  failed : ∀ prefix suffix → bytes ≡ prefix ++ suffix → Text → WriteReply bytes

data UnitReply : Set where completed : UnitReply; failed : Text → UnitReply

data SerializeReply : Set where
  serialized : List Byte → SerializeReply
  panicked : Text → SerializeReply

data Effect : Set where
  handleTool : Envelope.Text → JSON.Value → Effect
  formatTool : JSON.Value → Effect
  serialize : Response → Effect
  write : List Byte → Effect
  flush : Effect

Reply : Effect → Set
Reply (handleTool name args) = Text ⊎ JSON.Value
Reply (formatTool value) = Text ⊎ Text
Reply (serialize response) = SerializeReply
Reply (write bytes) = WriteReply bytes
Reply flush = UnitReply

module E = Effects.Protocol Effect Reply
open E public

data Failure : Set where
  formatting serialization writing flushing : Text → Failure

data Outcome : Set where nextLine : Outcome; stopped : Failure → Outcome

afterFlush : UnitReply → Script Outcome
afterFlush completed = done nextLine
afterFlush (failed message) = done (stopped (flushing message))

afterWrite : ∀ bytes → WriteReply bytes → Script Outcome
afterWrite bytes written = ask flush afterFlush
afterWrite bytes (failed prefix suffix exact message) = done (stopped (writing message))

afterSerialize : SerializeReply → Script Outcome
afterSerialize (panicked message) = done (stopped (serialization message))
afterSerialize (serialized bytes) = ask (write (bytes ++ (# 10 ∷ [])))
  (afterWrite (bytes ++ (# 10 ∷ [])))

emit : Response → Script Outcome
emit response = ask (serialize response) afterSerialize

respond : Envelope.Identity → Response → Script Outcome
respond identityValue response with Envelope.Identity.reply identityValue
... | false = done nextLine
... | true = emit response

afterFormat : Envelope.Identity → Text ⊎ Text → Script Outcome
afterFormat identityValue (inj₁ message) = done (stopped (formatting message))
afterFormat identityValue (inj₂ text) = respond identityValue (ok (Envelope.Identity.value identityValue) (content text))

afterTool : Envelope.Identity → Text ⊎ JSON.Value → Script Outcome
afterTool identityValue (inj₁ message) = respond identityValue (error (Envelope.Identity.value identityValue) -[1+ 31999 ] message)
afterTool identityValue (inj₂ value) = ask (formatTool value) (afterFormat identityValue)

dispatch : Envelope.Identity → Envelope.Command → Script Outcome
dispatch (Envelope.identity false id) command = done nextLine
dispatch (Envelope.identity true id) Envelope.initialize = emit (ok id initialized)
dispatch (Envelope.identity true id) Envelope.listTools = emit (ok id tools)
dispatch (Envelope.identity true id) (Envelope.callTool name args) =
  ask (handleTool name args) (afterTool (Envelope.identity true id))
dispatch (Envelope.identity true id) (Envelope.unknownMethod name) =
  emit (error id -[1+ 32600 ] (toList "Method not found"))
dispatch (Envelope.identity true id) (Envelope.invalidParams details) =
  emit (protocolProblem (Envelope.problem (Envelope.identity true id) -[1+ 32601 ] details))

exchange : Envelope.Problem ⊎ Envelope.Request → Script Outcome
exchange (inj₁ diagnostic) = respond (Envelope.Problem.response diagnostic) (protocolProblem diagnostic)
exchange (inj₂ invocation) = dispatch (Envelope.identityValue invocation) (Envelope.dispatch invocation)

parseError : Text → Script Outcome
parseError message = emit (protocolProblem (Envelope.problem
  (Envelope.identity true JSON.null) -[1+ 32699 ] (Envelope.Correction.claim
    (Envelope.Correction.item Envelope.Correction.request
      (V.fault [] V.malformedInput (fromList (toList "The request could not be parsed: " ++ message)))
      (toList "One complete UTF-8 JSON request object per line.")
      (toList "Repair the JSON syntax or UTF-8 encoding and resend the complete request with its client-chosen ID.")) [])))

-- Rejected input can only serialize and deliver its correction. This excludes
-- both business-handler execution and formatting a business result.
data ProtocolOnly : List Event → Set where
  empty : ProtocolOnly []
  serialization : ∀ response reply {events} → ProtocolOnly events →
    ProtocolOnly ((serialize response , reply) ∷ events)
  writing : ∀ bytes reply {events} → ProtocolOnly events →
    ProtocolOnly ((write bytes , reply) ∷ events)
  flushing : ∀ reply {events} → ProtocolOnly events →
    ProtocolOnly ((flush , reply) ∷ events)

flushOnly : ∀ reply events result → Runs (afterFlush reply) events result → ProtocolOnly events
flushOnly completed _ _ (returned _) = empty
flushOnly (failed _) _ _ (returned _) = empty

writeOnly : ∀ bytes reply events result → Runs (afterWrite bytes reply) events result → ProtocolOnly events
writeOnly bytes written _ _ (replied _ _ reply run) = flushing reply (flushOnly reply _ _ run)
writeOnly bytes (failed _ _ _ _) _ _ (returned _) = empty

serializeOnly : ∀ reply events result → Runs (afterSerialize reply) events result → ProtocolOnly events
serializeOnly (panicked _) _ _ (returned _) = empty
serializeOnly (serialized bytes) _ _ (replied _ _ reply run) =
  writing _ reply (writeOnly _ reply _ _ run)

invalidMethodParametersHaveNoBusinessEffects : ∀ id report events result →
  Runs (dispatch (Envelope.identity true id) (Envelope.invalidParams report)) events result →
  ProtocolOnly events
invalidMethodParametersHaveNoBusinessEffects id report events result (replied _ _ reply run) =
  serialization _ reply (serializeOnly reply _ _ run)

rejectedInputHasNoBusinessEffects : ∀ diagnostic events result →
  Runs (exchange (inj₁ diagnostic)) events result → ProtocolOnly events
rejectedInputHasNoBusinessEffects diagnostic events result run with Envelope.Identity.reply (Envelope.Problem.response diagnostic)
... | false with run
...   | returned _ = empty
rejectedInputHasNoBusinessEffects diagnostic events result (replied _ _ reply run) | true =
  serialization _ reply (serializeOnly reply _ _ run)

notificationHasNoEffects : ∀ id command events result →
  Runs (dispatch (Envelope.identity false id) command) events result →
  events ≡ [] × result ≡ nextLine
notificationHasNoEffects id command events result (returned _) = refl , refl

notificationSuccessEmitsNothing : ∀ id text events result →
  Runs (afterFormat (Envelope.identity false id) (inj₂ text)) events result →
  events ≡ [] × result ≡ nextLine
notificationSuccessEmitsNothing id text events result (returned _) = refl , refl

writeFailureStops : ∀ bytes prefix suffix exact message events result →
  Runs (afterWrite bytes (failed prefix suffix exact message)) events result →
  events ≡ [] × result ≡ stopped (writing message)
writeFailureStops bytes prefix suffix exact message events result (returned _) = refl , refl

flushFailureStops : ∀ message events result →
  Runs (afterFlush (failed message)) events result →
  events ≡ [] × result ≡ stopped (flushing message)
flushFailureStops message events result (returned _) = refl , refl
