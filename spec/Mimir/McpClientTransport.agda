{-# OPTIONS --safe #-}
-- Unbounded request supervision composed with concrete serialization,
-- write-all/flush and LF-framing receipts. Each finite execution is checked;
-- a still-running request has no fabricated completion or timeout receipt.
import Mimir.FloatConversion
module Mimir.McpClientTransport (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Bits using (Byte)
open import Mimir.Text using (Text)
open import Mimir.Validation using (Fault)
import Mimir.StructuredValue as V
import Mimir.McpClientRequest as RequestDependency
private module Request = RequestDependency floatConversion
import Mimir.McpClientLine as Line
import Mimir.McpSendBytes as Send
import Mimir.WriteAllFlush as Write
import Mimir.ReadLine as LF
import Mimir.Effects as Effects
import Mimir.EffectsHandling as Handling
import Mimir.EffectMap as Map
open import Mimir.McpTransportEffect public
module E = Effects.Protocol Effect Reply
module Mapping = Map.Protocol Effect Reply

sendOperation : ∀ operation → E.Script (Send.Reply operation)
sendOperation operation = E.ask (sending operation) E.done
module SendLower = Handling.With Send.Effect Send.Reply Effect Reply sendOperation

lineEvents : List Line.E.Event → List E.Event
lineEvents [] = []
lineEvents ((effect , reply) ∷ rest) = (receiving effect , reply) ∷ lineEvents rest

record Diagnostics : Set where
  field writeFailure : Write.Failure → Fault
        readFailure : Line.Failure → Fault

module With (diagnostics : Diagnostics) where
  module Framing = Line.Framing

  sendReply : ∀ {bytes} → Send.Outcome bytes → Fault ⊎ ⊤
  sendReply (Send.ioFailed reason) = inj₁ (Diagnostics.writeFailure diagnostics reason)
  sendReply (Send.delivered receipt) = inj₂ tt

  lineReply : Framing.Outcome → Fault ⊎ List Byte
  lineReply (Framing.failed reason) = inj₁ (Diagnostics.readFailure diagnostics reason)
  lineReply (Framing.complete accumulated) = inj₂ (Framing.Buffer.bytes accumulated)

  sendBody : List Byte → E.Script (Fault ⊎ ⊤)
  sendBody body = Mapping.map sendReply (SendLower.lower (Send.Send.start body))

  afterSerialization : Fault ⊎ List Byte → E.Script (Fault ⊎ ⊤)
  afterSerialization (inj₁ failure) = E.done (inj₁ failure)
  afterSerialization (inj₂ bytes) = sendBody bytes

  transmit : ℕ → Text → V.Value → E.Script (Fault ⊎ ⊤)
  transmit id method params = E.ask (serialize id method params) afterSerialization

  data Receipt : (operation : Request.Effect) → List E.Event → Request.Reply operation → Set where
    transmitted : ∀ id method params events reply → E.Runs (transmit id method params) events reply →
      Receipt (Request.send id method params) events reply
    received : ∀ events outcome → Framing.Runs Framing.start events outcome →
      Receipt Request.readLine (lineEvents events) (lineReply outcome)

  module Pending (expected : ℕ) where
    module R = Request.Pending expected
    start = R.start
    data Runs : R.State → List E.Event → Request.Outcome → Set where
      returned : ∀ outcome → Runs (R.finished outcome) [] outcome
      replied : ∀ {state effect continuation events rest outcome reply} →
        R.next state ≡ R.external effect continuation → Receipt effect events reply →
        Runs (continuation reply) rest outcome → Runs state (events ++ rest) outcome

    -- Low-level completion implies the exact same high-level request outcome.
    requestRefinement : ∀ {state events outcome} → Runs state events outcome →
      Σ (List Request.E.Event) (λ high → R.Runs state high outcome)
    requestRefinement (returned outcome) = [] , R.returned outcome
    requestRefinement (replied {effect = effect} {reply = reply} next receipt later)
      with requestRefinement later
    ... | high , execution = (effect , reply) ∷ high , R.replied next reply execution

  incomingNoLF : ∀ events accumulated → Framing.Runs Framing.start events (Framing.complete accumulated) →
    All LF.NotLF (Framing.Buffer.bytes accumulated)
  incomingNoLF events accumulated execution = Framing.Buffer.noLF accumulated

  record Outgoing (body : List Byte) (events : List E.Event) : Set where
    constructor outgoing
    field
      receipt : Send.Sent (Send.wire body)
      sendingEvents : List Send.E.Event
      sent : Send.E.Runs (Send.Send.start body) sendingEvents (Send.delivered receipt)
      translated : SendLower.Handled sendingEvents events

  outgoingReceipt : ∀ body events → E.Runs (sendBody body) events (inj₂ tt) → Outgoing body events
  outgoingReceipt body events execution with Mapping.backward sendReply
    (SendLower.lower (Send.Send.start body)) execution
  ... | Send.ioFailed reason , original , ()
  ... | Send.delivered receipt , original , refl
    with SendLower.refine (Send.Send.start body) original
  ... | SendLower.refinement sendingEvents sent translated = outgoing receipt sendingEvents sent translated

  outgoingExact : ∀ {body events} (receipt : Outgoing body events) →
    Send.Sent.actual (Outgoing.receipt receipt) ≡ Send.wire body
  outgoingExact {body} receipt = Send.Send.deliveredExactly body (Outgoing.receipt receipt)

  outgoingFlushed : ∀ {body events} (receipt : Outgoing body events) →
    Any (λ event → Write.flushReceipt event ≡ true) (Send.Sent.events (Outgoing.receipt receipt))
  outgoingFlushed {body} receipt = Send.Send.deliveredWasFlushed body (Outgoing.receipt receipt)

  serializationFailureStops : ∀ failure events result → E.Runs (afterSerialization (inj₁ failure)) events result → events ≡ []
  serializationFailureStops failure .[] .(inj₁ failure) (E.returned _) = refl
