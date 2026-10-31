{-# OPTIONS --safe #-}
-- One server exchange. Tool execution precedes notification suppression.
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
open import Data.String using (toList)
import Mimir.JsonStoredValue as JSON
import Mimir.McpEnvelope as Envelope
import Mimir.Effects as Effects

data Payload : Set where
  initialized tools : Payload
  content : Text → Payload

data Response : Set where
  ok : JSON.Value → Payload → Response
  error : JSON.Value → ℤ → Text → Response

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
dispatch identityValue Envelope.initialize = respond identityValue (ok (Envelope.Identity.value identityValue) initialized)
dispatch identityValue Envelope.listTools = respond identityValue (ok (Envelope.Identity.value identityValue) tools)
dispatch identityValue (Envelope.callTool name args) = ask (handleTool name args) (afterTool identityValue)
dispatch identityValue (Envelope.unknownMethod name) = respond identityValue
  (error (Envelope.Identity.value identityValue) -[1+ 32600 ] (toList "Method not found"))

exchange : Envelope.Request → Script Outcome
exchange invocation = dispatch (Envelope.Request.identityValue invocation) (Envelope.dispatch invocation)

parseError : Text → Script Outcome
parseError message = emit (error JSON.null -[1+ 32699 ] (toList "parse error: " ++ message))

notificationStillExecutes : ∀ id name args →
  dispatch (Envelope.identity false id) (Envelope.callTool name args) ≡
    ask (handleTool name args) (afterTool (Envelope.identity false id))
notificationStillExecutes id name args = refl

notificationFormatErrorStops : ∀ id message →
  afterFormat (Envelope.identity false id) (inj₁ message) ≡ done (stopped (formatting message))
notificationFormatErrorStops id message = refl

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
