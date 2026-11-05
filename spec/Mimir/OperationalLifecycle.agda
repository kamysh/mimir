{-# OPTIONS --safe #-}
-- New process startup and every watcher batch check compatibility before
-- database/model activity. Diagnostics/config commands remain available on a
-- rejected configuration. Operational log failures cannot start a batch.
module Mimir.OperationalLifecycle where
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.OperationalConfiguration as C
import Mimir.ConfigurationSchema as Schema
import Mimir.OperationalLogRetention as Log

data State : Set where
  reading : State
  logging : Schema.Config → State
  reviewing : Schema.Config → State
  blocked : Text → State
  waiting : ℕ → State

data Event : Set where
  configuration : Text ⊎ Schema.Config → Event
  logReady : Event
  logFailed : Text → Event
  batchFinished : ℕ → Event
  retry : Event

data Step : State → Event → State → Set where
  compatible : ∀ configurationValue → Step reading (configuration (inj₂ configurationValue)) (logging configurationValue)
  rejected : ∀ error → Step reading (configuration (inj₁ error)) (blocked error)
  ready : ∀ configurationValue → Step (logging configurationValue) logReady (reviewing configurationValue)
  failed : ∀ configurationValue error → Step (logging configurationValue) (logFailed error) (blocked error)
  completed : ∀ configurationValue delay → Step (reviewing configurationValue) (batchFinished delay) (waiting delay)
  retryBlocked : ∀ error → Step (blocked error) retry reading
  retryWaiting : ∀ delay → Step (waiting delay) retry reading

reviewRequiresLog : ∀ before event configurationValue → Step before event (reviewing configurationValue) →
  before ≡ logging configurationValue
reviewRequiresLog .(logging configurationValue) .logReady configurationValue (ready .configurationValue) = refl

reviewRequiresCompatible : ∀ before event configurationValue → Step before event (reviewing configurationValue) →
  C.Settings.version (C.Admitted.value (Schema.Config.operations configurationValue)) ≡ C.formatVersion
reviewRequiresCompatible before event configurationValue step = C.acceptedVersion (Schema.Config.operations configurationValue)

-- A wait/retry never reuses an already-loaded configuration. This matters
-- when settings change while a long-lived watcher is sleeping.
retryRevalidates : ∀ delay after → Step (waiting delay) retry after → after ≡ reading
retryRevalidates delay .reading (retryWaiting .delay) = refl

record RuntimeReceipt : Set where
  constructor receipt
  field packageVersion : Text; processId : ℕ; nextAttempt : Maybe ℕ; failures : ℕ
-- A receipt describes observed activity; its presence does not prove a process
-- remains alive. UI labels this as a snapshot, not a liveness assertion.
