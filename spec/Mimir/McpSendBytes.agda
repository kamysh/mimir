{-# OPTIONS --safe #-}
-- Outgoing byte layer after serialization: one LF and one write-all/flush
-- attempt, without an application size or time cutoff. Serialization itself
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
  transmit : List Byte → Effect

Reply : Effect → Set
Reply (transmit bytes) = IOReport bytes

module E = Effects.Protocol Effect Reply
module Count = E.Counting (λ _ → 1)

record Sent (bytes : List Byte) : Set where
  constructor sentReceipt
  field
    events : List Write.Event
    actual : List Byte
    trace : Write.Trace (Write.initial bytes) events (Write.complete actual)

data Outcome (bytes : List Byte) : Set where
  ioFailed : Write.Failure → Outcome bytes
  delivered : Sent bytes → Outcome bytes

wire : List Byte → List Byte
wire bytes = bytes ++ (# 10 ∷ [])

wireLength : ∀ bytes → length (wire bytes) ≡ suc (length bytes)
wireLength bytes = trans (length-++ bytes {ys = # 10 ∷ []})
  (trans (+-suc (length bytes) 0) (cong suc (+-identityʳ (length bytes))))

module Send (body : List Byte) where
  Result = Outcome (wire body)

  afterIO : IOReport (wire body) → E.Script Result
  afterIO (sent events actual proof) = E.done (delivered (sentReceipt events actual proof))
  afterIO (failed events before reply failure proof exact) = E.done (ioFailed failure)

  start : E.Script Result
  start = E.ask (transmit (wire body)) afterIO

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
    delivered : DeliveryTrace receipt
      ((transmit (wire body) , sent (Sent.events receipt) (Sent.actual receipt) (Sent.trace receipt)) ∷ [])

  everyDeliveryChecked : ∀ events receipt → E.Runs start events (delivered receipt) → DeliveryTrace receipt events
  everyDeliveryChecked .((transmit (wire body) , report) ∷ events) receipt
    (E.replied .(transmit (wire body)) _ report {events} execution)
    with ioSuccess report events receipt execution
  ... | refl , refl = delivered
