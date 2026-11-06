{-# OPTIONS --safe #-}
-- One client request. IDs advance before sending, notifications consume a
-- no allowance, and no failure retries a write. The readLine effect is
-- refined separately into an unbounded byte-framing state machine.
import Mimir.StandardLibrary
module Mimir.McpClientRequest (library : Mimir.StandardLibrary.Contract) where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_)
open import Data.Nat.Properties using (≤-refl; +-suc; 1+n≰n)
open import Data.Product using (_,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst; sym)
open import Mimir.Text using (Text)
open import Mimir.Validation using (Fault)
import Mimir.StructuredValue as V
import Mimir.McpClientWire as WireDependency
private
  module Wire = WireDependency library
import Mimir.RpcReply as RPC
import Mimir.Bits as Bits
import Mimir.Effects as Effects

module R = Wire.Replies

data Effect : Set where
  send : ℕ → Text → V.Value → Effect
  readLine : Effect

Reply : Effect → Set
Reply (send id method params) = Fault ⊎ ⊤
Reply readLine = Fault ⊎ List Bits.Byte

module E = Effects.Protocol Effect Reply
module Count = E.Counting (λ _ → 1)

data Outcome : Set where
  transportFailure syntaxFailure : Fault → Outcome
  protocolFailure : RPC.Failure → Outcome
  applicationFailure success : V.Value → Outcome

module Pending (expected : ℕ) where
  data State : Set where
    sending : Text → V.Value → State
    waiting : ℕ → State
    finished : Outcome → State

  afterLine : ℕ → Reply readLine → State
  afterLine notices (inj₁ failure) = finished (transportFailure failure)
  afterLine notices (inj₂ bytes) with Wire.line bytes
  ... | inj₁ failure = finished (syntaxFailure failure)
  ... | inj₂ raw with Wire.receive expected notices raw
  ...   | R.failed failure = finished (protocolFailure failure)
  ...   | R.rejected failure = finished (applicationFailure failure)
  ...   | R.succeeded value = finished (success value)
  ...   | R.notification next = waiting next

  afterSend : Reply (send expected [] V.null) → State
  afterSend (inj₁ failure) = finished (transportFailure failure)
  afterSend (inj₂ tt) = waiting 0

  data Step : Set where
    external : (effect : Effect) → (Reply effect → State) → Step
    stopped : Outcome → Step

  next : State → Step
  next (sending method params) = external (send expected method params) afterSend
  next (waiting notices) = external readLine (afterLine notices)
  next (finished result) = stopped result

  data Runs : State → List E.Event → Outcome → Set where
    returned : ∀ outcome → Runs (finished outcome) [] outcome
    replied : ∀ {state effect continuation events outcome} → next state ≡ external effect continuation →
      (reply : Reply effect) → Runs (continuation reply) events outcome →
      Runs state ((effect , reply) ∷ events) outcome

  -- Cancellation retains a real unfinished request cursor, including a send
  -- that may already have reached the service. It invents no reply or rollback.
  data Prefix : State → List E.Event → State → Set where
    stopped : ∀ state → Prefix state [] state
    replied : ∀ {state effect continuation events after} → next state ≡ external effect continuation →
      (reply : Reply effect) → Prefix (continuation reply) events after →
      Prefix state ((effect , reply) ∷ events) after

  start : Text → V.Value → State
  start = sending

  failedSendStops : ∀ failure → afterSend (inj₁ failure) ≡ finished (transportFailure failure)
  failedSendStops failure = refl

module Counter (maximum : ℕ) where
  module IDs = RPC.IDs maximum

  data Launch : Set where
    overflow : Launch
    started : (current next : ℕ) → Pending.State current → Launch

  launch : ℕ → Text → V.Value → Launch
  launch counter method params with IDs.allocate counter
  ... | nothing = overflow
  ... | just allocation = started (IDs.Allocated.current allocation) (IDs.Allocated.next allocation)
    (Pending.start (IDs.Allocated.current allocation) method params)

  launchAdvances : ∀ counter method params current next program →
    launch counter method params ≡ started current next program → current < next
  launchAdvances counter method params current next program observed with IDs.allocate counter in allocation
  ... | nothing with observed
  ...   | ()
  launchAdvances counter method params ._ ._ ._ refl | just reserved = IDs.advances counter reserved allocation
