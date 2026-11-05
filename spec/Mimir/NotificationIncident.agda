{-# OPTIONS --safe #-}
-- Incident reconciliation does not deliver mail. It preserves retry state
-- for a repeated failure and emits recovery only for a previously delivered
-- failure. Alert identity is explicit input, not a uniqueness postulate.
module Mimir.NotificationIncident where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.String using (toList)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)

data Status : Set where
  failure : Text → Text → Status
  progress recovery : Status

record Event : Set where
  constructor event
  field source incidentKey : Text; status : Status; details : Maybe Text

data Kind : Set where failure recovery : Kind
data Delivery : Set where pending exhausted : Delivery
data LastError : Set where authRequired unavailable : LastError

record Alert : Set where
  constructor alert
  field
    identity : Text
    kind : Kind
    source code summary : Text
    details : Maybe Text
    attempts nextDue : ℕ
    delivery : Delivery
    lastError : Maybe LastError

record Incident : Set where
  constructor incident
  field
    source incidentKey : Text
    activeCode deliveredCode : Maybe Text
    outbox : Maybe Alert

newAlert : Text → ℕ → Kind → Event → Text → Text → Alert
newAlert identity now kind e code summary = alert identity kind (Event.source e) code summary
  (Event.details e) 0 now pending nothing

recoverAlert : Text → ℕ → Event → Maybe Text → Maybe Alert
recoverAlert identity now e nothing = nothing
recoverAlert identity now e (just delivered) = just (newAlert identity now recovery e delivered (toList "Recovered"))

newFailure : Text → ℕ → Incident → Event → Text → Text → Incident
newFailure identity now before e code summary = record before
  { activeCode = just code ; outbox = just (newAlert identity now failure e code summary) }

reconcile : Text → ℕ → Incident → Event → Incident
reconcile identity now before e with Event.status e
... | progress = before
... | recovery with Incident.activeCode before
...   | nothing = before
...   | just active = record before
  { activeCode = nothing ; outbox = recoverAlert identity now e (Incident.deliveredCode before) }
reconcile identity now before e | failure code summary with Incident.activeCode before
... | nothing = newFailure identity now before e code summary
... | just active with active ≟Text code
...   | yes same = before
...   | no different = newFailure identity now before e code summary

duplicateFailurePreservesAllState : ∀ identity now before source key code summary details →
  Incident.activeCode before ≡ just code →
  reconcile identity now before (event source key (failure code summary) details) ≡ before
duplicateFailurePreservesAllState identity now before source key code summary details active
  rewrite active with code ≟Text code
... | yes _ = refl
... | no impossible = ⊥-elim (impossible refl)

progressPreservesIncident : ∀ identity now before source key details →
  reconcile identity now before (event source key progress details) ≡ before
progressPreservesIncident identity now before source key details = refl

unsentFailureHasNoRecoveryAlert : ∀ identity now before source key details active →
  Incident.activeCode before ≡ just active → Incident.deliveredCode before ≡ nothing →
  Incident.outbox (reconcile identity now before (event source key recovery details)) ≡ nothing
unsentFailureHasNoRecoveryAlert identity now before source key details active activeEqual notDelivered
  rewrite activeEqual | notDelivered = refl

repeatedRecoveryPreservesRetry : ∀ identity now before source key details →
  Incident.activeCode before ≡ nothing →
  reconcile identity now before (event source key recovery details) ≡ before
repeatedRecoveryPreservesRetry identity now before source key details inactive rewrite inactive = refl

data Outcome : Set where
  disabled notNeeded sent retryPending exhausted authRequired unavailable : Outcome

outcome : Incident → Outcome
outcome before with Incident.outbox before
... | nothing = notNeeded
... | just a with Alert.delivery a
...   | exhausted = exhausted
...   | pending with Alert.lastError a
...     | nothing = retryPending
...     | just authRequired = authRequired
...     | just unavailable = unavailable

-- SMTP success changes only delivered-code bookkeeping and the queued alert.
-- The active failure episode is cleared by a recovery event, not by sending.
accepted : Incident → Alert → Incident
accepted before a with Alert.kind a
... | failure = record before { deliveredCode = just (Alert.code a) ; outbox = nothing }
... | recovery = record before { deliveredCode = nothing ; outbox = nothing }

acceptedDoesNotResolveIncident : ∀ before a → Incident.activeCode (accepted before a) ≡ Incident.activeCode before
acceptedDoesNotResolveIncident before a with Alert.kind a
... | failure = refl
... | recovery = refl

acceptedClearsOnlyQueuedAlert : ∀ before a → Incident.outbox (accepted before a) ≡ nothing
acceptedClearsOnlyQueuedAlert before a with Alert.kind a
... | failure = refl
... | recovery = refl
