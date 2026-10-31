{-# OPTIONS --safe #-}
-- One client request. IDs advance before sending, notifications consume a
-- finite allowance, and no failure retries a write. The readLine effect is
-- refined separately into byte reads and a deadline.
import Mimir.FloatConversion
module Mimir.McpClientRequest (floatConversion : Mimir.FloatConversion.Contract) where

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
  module Wire = WireDependency floatConversion
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

notificationFacts : ∀ expected notices raw next → Wire.receive expected notices raw ≡ R.notification next →
  next ≡ suc notices × next ≤ 64
notificationFacts expected notices raw next observed =
  R.notificationAdvances expected notices (Wire.extract raw) next identified ,
  R.notificationBound expected notices (Wire.extract raw) next identified
  where
  identified = R.receivedNotification expected notices (Wire.extract raw) next observed

exhaustedCannotNotify : ∀ expected notices raw next → notices ≡ 64 →
  Wire.receive expected notices raw ≡ R.notification next → ⊥
exhaustedCannotNotify expected notices raw next exhausted observed
  with notificationFacts expected notices raw next observed
... | advance , bounded rewrite advance | exhausted = 1+n≰n bounded

module Pending (expected : ℕ) where
  mutual
    wait : ∀ remaining notices → remaining + notices ≡ 64 → E.Script Outcome
    wait remaining notices allowance = E.ask readLine (afterLine remaining notices allowance)

    afterLine : ∀ remaining notices → remaining + notices ≡ 64 → Reply readLine → E.Script Outcome
    afterLine remaining notices allowance (inj₁ failure) = E.done (transportFailure failure)
    afterLine remaining notices allowance (inj₂ bytes) with Wire.line bytes
    ... | inj₁ failure = E.done (syntaxFailure failure)
    ... | inj₂ raw = afterFrame remaining notices allowance raw (Wire.receive expected notices raw) refl

    afterFrame : ∀ remaining notices → remaining + notices ≡ 64 → ∀ raw outcome →
      Wire.receive expected notices raw ≡ outcome → E.Script Outcome
    afterFrame remaining notices allowance raw (R.failed failure) observed = E.done (protocolFailure failure)
    afterFrame remaining notices allowance raw (R.rejected failure) observed = E.done (applicationFailure failure)
    afterFrame remaining notices allowance raw (R.succeeded value) observed = E.done (success value)
    afterFrame zero notices allowance raw (R.notification next) observed =
      ⊥-elim (exhaustedCannotNotify expected notices raw next allowance observed)
    afterFrame (suc remaining) notices allowance raw (R.notification next) observed
      with notificationFacts expected notices raw next observed
    ... | advance , bounded = wait remaining next
      (trans (subst (λ n → remaining + n ≡ suc (remaining + notices)) (sym advance) (+-suc remaining notices)) allowance)

  afterSend : Reply (send expected [] V.null) → E.Script Outcome
  afterSend (inj₁ failure) = E.done (transportFailure failure)
  afterSend (inj₂ tt) = wait 64 0 refl

  start : Text → V.Value → E.Script Outcome
  start method params = E.ask (send expected method params) afterSend

  mutual
    waitBound : ∀ remaining notices allowance → Count.Bounded (suc remaining) (wait remaining notices allowance)
    waitBound remaining notices allowance = Count.ask readLine _ remaining ≤-refl (lineBound remaining notices allowance)

    lineBound : ∀ remaining notices allowance reply →
      Count.Bounded remaining (afterLine remaining notices allowance reply)
    lineBound remaining notices allowance (inj₁ failure) = Count.done _
    lineBound remaining notices allowance (inj₂ bytes) with Wire.line bytes
    ... | inj₁ failure = Count.done _
    ... | inj₂ raw = frameBound remaining notices allowance raw _ refl

    frameBound : ∀ remaining notices allowance raw outcome observed →
      Count.Bounded remaining (afterFrame remaining notices allowance raw outcome observed)
    frameBound remaining notices allowance raw (R.failed failure) observed = Count.done _
    frameBound remaining notices allowance raw (R.rejected failure) observed = Count.done _
    frameBound remaining notices allowance raw (R.succeeded value) observed = Count.done _
    frameBound zero notices allowance raw (R.notification next) observed =
      ⊥-elim (exhaustedCannotNotify expected notices raw next allowance observed)
    frameBound (suc remaining) notices allowance raw (R.notification next) observed
      with notificationFacts expected notices raw next observed
    ... | advance , bounded = waitBound remaining next _

  sendBound : ∀ reply → Count.Bounded 65 (afterSend reply)
  sendBound (inj₁ failure) = Count.done _
  sendBound (inj₂ tt) = waitBound 64 0 refl

  bounded : ∀ method params → Count.Bounded 66 (start method params)
  bounded method params = Count.ask (send expected method params) afterSend 65 ≤-refl sendBound

  finiteRequest : ∀ method params events outcome → E.Runs (start method params) events outcome → Count.count events ≤ 66
  finiteRequest method params events outcome execution = Count.runBounded (bounded method params) execution

  finitePrefix : ∀ method params events residual → E.Prefix (start method params) events residual → Count.count events ≤ 66
  finitePrefix method params events residual execution = Count.prefixBounded (bounded method params) execution

  failedSendStops : ∀ failure events outcome → E.Runs (afterSend (inj₁ failure)) events outcome →
    events ≡ [] × outcome ≡ transportFailure failure
  failedSendStops failure events outcome execution = E.completedCannotProduceEffects execution

module Counter (maximum : ℕ) where
  module IDs = RPC.IDs maximum

  data Launch : Set where
    overflow : Launch
    started : (current next : ℕ) → E.Script Outcome → Launch

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
