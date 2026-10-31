{-# OPTIONS --safe #-}
-- Compose request supervision with the actual send/framing protocols.
-- Serialization receipts and diagnostic rendering remain explicit boundaries;
-- they are not treated as proved JSON encoding or native I/O implementations.
import Mimir.FloatConversion
module Mimir.McpClientTransport (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.Nat using (ℕ; _≤_)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Mimir.Bits using (Byte)
open import Mimir.Text using (Text)
open import Mimir.Validation using (Fault)
import Mimir.StructuredValue as V
import Mimir.McpClientRequest as RequestDependency
private
  module Request = RequestDependency floatConversion
import Mimir.McpClientLine as Line
import Mimir.McpClientLineLaws as LineLaws
import Mimir.McpSendBytes as Send
import Mimir.WriteAllFlush as Write
import Mimir.ReadLine as LF
import Mimir.Effects as Effects
import Mimir.EffectsHandling as Handling
import Mimir.EffectsHandlingPrefix as Partial
import Mimir.EffectMap as Map

open import Mimir.McpTransportEffect public

module E = Effects.Protocol Effect Reply
module Mapping = Map.Protocol Effect Reply

sendOperation : ∀ operation → E.Script (Send.Reply operation)
sendOperation operation = E.ask (sending operation) E.done

lineOperation : ∀ operation → E.Script (Line.Reply operation)
lineOperation operation = E.ask (receiving operation) E.done

module SendLower = Handling.With Send.Effect Send.Reply Effect Reply sendOperation
module LineLower = Handling.With Line.Effect Line.Reply Effect Reply lineOperation

record Diagnostics : Set where
  field
    requestTooLarge deadlineExceeded : Fault
    writeFailure : Write.Failure → Fault
    readFailure : Line.Failure → Fault

module With (maximum deadline : ℕ) (diagnostics : Diagnostics) where
  module Framing = Line.Framing maximum deadline
  module Framed = LineLaws.Laws maximum deadline

  sendReply : ∀ {bytes} → Send.Outcome bytes → Fault ⊎ ⊤
  sendReply Send.tooLarge = inj₁ (Diagnostics.requestTooLarge diagnostics)
  sendReply Send.deadlineExceeded = inj₁ (Diagnostics.deadlineExceeded diagnostics)
  sendReply (Send.ioFailed reason) = inj₁ (Diagnostics.writeFailure diagnostics reason)
  sendReply (Send.delivered receipt) = inj₂ tt

  lineReply : Framing.Outcome → Fault ⊎ List Byte
  lineReply (Framing.failed reason) = inj₁ (Diagnostics.readFailure diagnostics reason)
  lineReply (Framing.complete remaining accumulated) = inj₂ (Framing.Buffer.bytes accumulated)

  sendBody : List Byte → E.Script (Fault ⊎ ⊤)
  sendBody body = Mapping.map sendReply (SendLower.lower (Send.Send.start maximum deadline body))

  afterSerialization : Fault ⊎ List Byte → E.Script (Fault ⊎ ⊤)
  afterSerialization (inj₁ failure) = E.done (inj₁ failure)
  afterSerialization (inj₂ bytes) = sendBody bytes

  readLine : E.Script (Fault ⊎ List Byte)
  readLine = Mapping.map lineReply (LineLower.lower Framing.start)

  implementation : ∀ operation → E.Script (Request.Reply operation)
  implementation (Request.send identity method params) = E.ask (serialize identity method params) afterSerialization
  implementation Request.readLine = readLine

  module Lower = Handling.With Request.Effect Request.Reply Effect Reply implementation
  module Interrupted = Partial.With Request.Effect Request.Reply Effect Reply implementation

  start : ℕ → Text → V.Value → E.Script Request.Outcome
  start identity method params = Lower.lower (Request.Pending.start identity method params)

  requestRefinement : ∀ identity method params events result → E.Runs (start identity method params) events result →
    Lower.Refinement (Request.Pending.start identity method params) events result
  requestRefinement identity method params events result execution = Lower.refine (Request.Pending.start identity method params)
    execution

  boundedRequests : ∀ identity method params events result (execution : E.Runs (start identity method params) events result) →
    Request.Count.count (Lower.Refinement.highEvents
      (requestRefinement identity method params events result execution)) ≤ 66
  boundedRequests identity method params events result execution = Request.Pending.finiteRequest identity method params _ result
    (Lower.Refinement.highRun
     (requestRefinement identity method params events result execution))

  interruptedRefinement : ∀ identity method params events residual →
    E.Prefix (start identity method params) events residual →
    Interrupted.Partial (Request.Pending.start identity method params) events residual
  interruptedRefinement identity method params events residual execution = Interrupted.reflect (Request.Pending.start identity method params)
    execution

  interruptedBound : ∀ identity method params events residual
    (execution : E.Prefix (start identity method params) events residual) →
    Request.Count.count (Interrupted.completedEvents
      (interruptedRefinement identity method params events residual execution)) ≤ 66
  interruptedBound identity method params events residual execution = Request.Pending.finitePrefix identity method params _ _
    (Interrupted.project
     (interruptedRefinement identity method params events residual
      execution))

  record Incoming (events : List E.Event) (bytes : List Byte) : Set where
    constructor incoming
    field
      remaining : ℕ
      buffer : Framing.Buffer remaining
      framingEvents : List Line.E.Event
      framed : Line.E.Runs Framing.start framingEvents (Framing.complete remaining buffer)
      translated : LineLower.Handled framingEvents events
      exact : Framing.Buffer.bytes buffer ≡ bytes

  incomingReceipt : ∀ events bytes → E.Runs readLine events (inj₂ bytes) → Incoming events bytes
  incomingReceipt events bytes execution with Mapping.backward lineReply (LineLower.lower Framing.start) execution
  ... | Framing.failed reason , original , ()
  ... | Framing.complete remaining accumulated , original , refl
    with LineLower.refine Framing.start original
  ... | LineLower.refinement framingEvents framed translated = incoming remaining accumulated framingEvents framed translated refl

  incomingFramed : ∀ {events bytes} (receipt : Incoming events bytes) →
    Framed.Frame (Incoming.framingEvents receipt) bytes
  incomingFramed receipt = subst (Framed.Frame (Incoming.framingEvents receipt))
    (Incoming.exact receipt)
    (Framed.completeFramed (Incoming.framingEvents receipt)
     (Incoming.remaining receipt) (Incoming.buffer receipt)
     (Incoming.framed receipt))

  incomingBounded : ∀ {events bytes} → Incoming events bytes → length bytes ≤ maximum
  incomingBounded receipt = subst (λ bytes → length bytes ≤ maximum) (Incoming.exact receipt)
    (Framed.capacityBound (Incoming.remaining receipt)
     (Incoming.buffer receipt))

  incomingNoLF : ∀ {events bytes} → Incoming events bytes → All LF.NotLF bytes
  incomingNoLF receipt = subst (All LF.NotLF) (Incoming.exact receipt)
    (Framed.successfulBodyContainsNoLF (Incoming.remaining receipt)
     (Incoming.buffer receipt))

  record Outgoing (body : List Byte) (events : List E.Event) : Set where
    constructor outgoing
    field
      receipt : Send.Sent (Send.wire body)
      sendingEvents : List Send.E.Event
      sent : Send.E.Runs (Send.Send.start maximum deadline body) sendingEvents (Send.delivered receipt)
      translated : SendLower.Handled sendingEvents events

  outgoingReceipt : ∀ body events → E.Runs (sendBody body) events (inj₂ tt) → Outgoing body events
  outgoingReceipt body events execution with Mapping.backward sendReply
    (SendLower.lower (Send.Send.start maximum deadline body)) execution
  ... | Send.tooLarge , original , ()
  ... | Send.deadlineExceeded , original , ()
  ... | Send.ioFailed reason , original , ()
  ... | Send.delivered receipt , original , refl
    with SendLower.refine (Send.Send.start maximum deadline body) original
  ... | SendLower.refinement sendingEvents sent translated = outgoing receipt sendingEvents sent translated

  outgoingExact : ∀ {body events} (receipt : Outgoing body events) →
    Send.Sent.actual (Outgoing.receipt receipt) ≡ Send.wire body
  outgoingExact {body} receipt = Send.Send.deliveredExactly maximum deadline body
    (Outgoing.receipt receipt)

  outgoingFlushed : ∀ {body events} (receipt : Outgoing body events) →
    Any (λ event → Write.flushReceipt event ≡ true) (Send.Sent.events (Outgoing.receipt receipt))
  outgoingFlushed {body} receipt = Send.Send.deliveredWasFlushed maximum deadline body
    (Outgoing.receipt receipt)

  serializationFailureStops : ∀ failure events result → E.Runs (afterSerialization (inj₁ failure)) events result →
    events ≡ []
  serializationFailureStops failure .[] .(inj₁ failure) (E.returned _) = refl
