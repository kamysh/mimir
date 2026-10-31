{-# OPTIONS --safe #-}
-- Outgoing byte layer after serialization: strict body limit, one LF,
-- one deadline check and one write-all/flush attempt. Serialization itself
-- is a separate obligation; an arbitrary byte list is not a JSON proof.
module Mimir.McpSendBytes where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.Bool using (true)
open import Data.Fin using (#_)
open import Data.Nat using (ℕ; _+_; _∸_; _≤_; _<_; _<?_; suc)
open import Data.Nat.Properties using (≤-refl; ≤-trans; 1+n≰n; +-suc; +-identityʳ)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import Mimir.Bits using (Byte)
import Mimir.WriteAllFlush as Write
import Mimir.Effects as Effects

data IOReport (bytes : List Byte) : Set where
  sent : ∀ events actual → Write.Trace (Write.initial bytes) events (Write.complete actual) → IOReport bytes
  failed : ∀ events before reply failure → Write.Trace (Write.initial bytes) events before →
    Write.Result.reason (Write.step before reply) ≡ just failure → IOReport bytes

data Effect : Set where
  clockNow : Effect
  transmit : ℕ → List Byte → Effect

Reply : Effect → Set
Reply clockNow = ℕ
Reply (transmit duration bytes) = IOReport bytes

module E = Effects.Protocol Effect Reply
module Count = E.Counting (λ _ → 1)

record Sent (bytes : List Byte) : Set where
  constructor sentReceipt
  field
    events : List Write.Event
    actual : List Byte
    trace : Write.Trace (Write.initial bytes) events (Write.complete actual)

data Outcome (bytes : List Byte) : Set where
  tooLarge deadlineExceeded : Outcome bytes
  ioFailed : Write.Failure → Outcome bytes
  delivered : Sent bytes → Outcome bytes

wire : List Byte → List Byte
wire bytes = bytes ++ (# 10 ∷ [])

wireLength : ∀ bytes → length (wire bytes) ≡ suc (length bytes)
wireLength bytes = trans (length-++ bytes {ys = # 10 ∷ []})
  (trans (+-suc (length bytes) 0) (cong suc (+-identityʳ (length bytes))))

module Send (maximum deadline : ℕ) (body : List Byte) where
  Result = Outcome (wire body)

  afterIO : IOReport (wire body) → E.Script Result
  afterIO (sent events actual proof) = E.done (delivered (sentReceipt events actual proof))
  afterIO (failed events before reply failure proof exact) = E.done (ioFailed failure)

  afterClock : ℕ → E.Script Result
  afterClock now with now <? deadline
  ... | no expired = E.done deadlineExceeded
  ... | yes available = E.ask (transmit (deadline ∸ now) (wire body)) afterIO

  start : E.Script Result
  start with length body <? maximum
  ... | no oversized = E.done tooLarge
  ... | yes fits = E.ask clockNow afterClock

  ioBound : ∀ reply → Count.Bounded 0 (afterIO reply)
  ioBound (sent events actual proof) = Count.done _
  ioBound (failed events before reply failure proof exact) = Count.done _

  clockBound : ∀ now → Count.Bounded 1 (afterClock now)
  clockBound now with now <? deadline
  ... | no expired = Count.done _
  ... | yes available = Count.ask (transmit (deadline ∸ now) (wire body)) afterIO 0 ≤-refl ioBound

  bounded : Count.Bounded 2 start
  bounded with length body <? maximum
  ... | no oversized = Count.done _
  ... | yes fits = Count.ask clockNow afterClock 1 ≤-refl clockBound

  finiteSend : ∀ events result → E.Runs start events result → Count.count events ≤ 2
  finiteSend events result execution = Count.runBounded bounded execution

  finitePrefix : ∀ events residual → E.Prefix start events residual → Count.count events ≤ 2
  finitePrefix events residual execution = Count.prefixBounded bounded execution

  oversizedStops : maximum ≤ length body → start ≡ E.done tooLarge
  oversizedStops oversized with length body <? maximum
  ... | no doesNotFit = refl
  ... | yes fits = ⊥-elim (1+n≰n (≤-trans fits oversized))

  expiredStops : ∀ now → deadline ≤ now → afterClock now ≡ E.done deadlineExceeded
  expiredStops now expired with now <? deadline
  ... | no unavailable = refl
  ... | yes available = ⊥-elim (1+n≰n (≤-trans available expired))

  wireFits : length body < maximum → length (wire body) ≤ maximum
  wireFits fits = subst (_≤ maximum) (sym (wireLength body)) fits

  deliveredExactly : ∀ (receipt : Sent (wire body)) → Sent.actual receipt ≡ wire body
  deliveredExactly receipt = Write.completedBytesExact (wire body) (Sent.events receipt) (Sent.actual receipt) (Sent.trace receipt)

  deliveredWasFlushed : ∀ (receipt : Sent (wire body)) →
    Any (λ event → Write.flushReceipt event ≡ true) (Sent.events receipt)
  deliveredWasFlushed receipt = Write.successfulSendWasFlushed (wire body)
    (Sent.events receipt) (Sent.actual receipt) (Sent.trace receipt)

  ioSuccess : ∀ report events receipt → E.Runs (afterIO report) events (delivered receipt) →
    events ≡ [] × report ≡ sent (Sent.events receipt) (Sent.actual receipt) (Sent.trace receipt)
  ioSuccess (sent events actual proof) .[] .(sentReceipt events actual proof) (E.returned _) = refl , refl
  ioSuccess (failed events before reply failure proof exact) trace receipt ()

  data DeliveryTrace (receipt : Sent (wire body)) : List E.Event → Set where
    deliveredAt : ∀ now → length body < maximum → now < deadline → DeliveryTrace receipt
      ((clockNow , now) ∷ (transmit (deadline ∸ now) (wire body) ,
        sent (Sent.events receipt) (Sent.actual receipt) (Sent.trace receipt)) ∷ [])

  clockTrace : ∀ now → length body < maximum → ∀ events receipt →
    E.Runs (afterClock now) events (delivered receipt) → DeliveryTrace receipt ((clockNow , now) ∷ events)
  clockTrace now admitted events receipt execution with now <? deadline
  ... | no expired with execution
  ...   | ()
  clockTrace now admitted .((transmit (deadline ∸ now) (wire body) , report) ∷ events) receipt
    (E.replied .(transmit (deadline ∸ now) (wire body)) _ report {events} execution) | yes available
    with ioSuccess report events receipt execution
  ... | refl , refl = deliveredAt now admitted available

  everyDeliveryChecked : ∀ events receipt → E.Runs start events (delivered receipt) → DeliveryTrace receipt events
  everyDeliveryChecked events receipt execution with length body <? maximum
  ... | no oversized with execution
  ...   | ()
  everyDeliveryChecked .((clockNow , now) ∷ events) receipt
    (E.replied .clockNow _ now {events} execution) | yes admitted = clockTrace now admitted events receipt execution
