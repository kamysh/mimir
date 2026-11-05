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
  compatible : ∀ config → Step reading (configuration (inj₂ config)) (logging config)
  rejected : ∀ error → Step reading (configuration (inj₁ error)) (blocked error)
  ready : ∀ config → Step (logging config) logReady (reviewing config)
  failed : ∀ config error → Step (logging config) (logFailed error) (blocked error)
  completed : ∀ config delay → Step (reviewing config) (batchFinished delay) (waiting delay)
  retryBlocked : ∀ error → Step (blocked error) retry reading
  retryWaiting : ∀ delay → Step (waiting delay) retry reading

reviewRequiresLog : ∀ before event config → Step before event (reviewing config) →
  before ≡ logging config
reviewRequiresLog .(logging config) .logReady config (ready .config) = refl

reviewRequiresCompatible : ∀ before event config → Step before event (reviewing config) →
  C.Settings.version (C.Admitted.value (Schema.Config.operations config)) ≡ C.formatVersion
reviewRequiresCompatible before event config step = C.acceptedVersion (Schema.Config.operations config)

-- A wait/retry never reuses an already-loaded configuration. This matters
-- when settings change while a long-lived watcher is sleeping.
retryRevalidates : ∀ delay after → Step (waiting delay) retry after → after ≡ reading
retryRevalidates delay .reading (retryWaiting .delay) = refl

record RuntimeReceipt : Set where
  constructor receipt
  field packageVersion : Text; processId : ℕ; nextAttempt : Maybe ℕ; failures : ℕ
-- A receipt describes observed activity; its presence does not prove a process
-- remains alive. UI labels this as a snapshot, not a liveness assertion.
