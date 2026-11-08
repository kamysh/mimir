{-# OPTIONS --safe #-}
-- New process startup and every watcher batch check compatibility before
-- database/model activity. Diagnostics/config commands remain available on a
-- rejected configuration. Operational log failures cannot start a batch.
module Mimir.OperationalLifecycle where
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Mimir.Text using (Text)
import Mimir.OperationalConfiguration as C
import Mimir.ConfigurationSchema as Schema
import Mimir.OperationalLogRetention as Log
import Mimir.OperationalLogProtocol as Logging

logs : Schema.Config → C.Logging
logs configurationValue = C.Settings.logs (C.Admitted.value (Schema.Config.operations configurationValue))

module LogAt (configurationValue : Schema.Config) =
  Logging.For (C.Logging.directory (logs configurationValue))

record LogAttempt (configurationValue : Schema.Config) : Set where
  field
    entry : List Log.Byte
    events : List (LogAt.Event configurationValue)
    outcome : LogAt.Outcome configurationValue
    completed : LogAt.Attempt configurationValue entry events outcome

data State : Set where
  reading : State
  logging : Schema.Config → State
  reviewing : Schema.Config → State
  blocked : Text → State
  waiting : ℕ → State

data Event : Set where
  configuration : Text ⊎ Schema.Config → Event
  logCompleted : ∀ configurationValue → LogAttempt configurationValue → Event
  batchFinished : ℕ → Event
  retry : Event

data Step : State → Event → State → Set where
  compatible : ∀ configurationValue → Step reading (configuration (inj₂ configurationValue)) (logging configurationValue)
  rejected : ∀ error → Step reading (configuration (inj₁ error)) (blocked error)
  ready : ∀ configurationValue (observed : LogAttempt configurationValue) files →
    LogAttempt.outcome observed ≡ LogAt.written {configurationValue} files →
    Step (logging configurationValue) (logCompleted configurationValue observed) (reviewing configurationValue)
  failed : ∀ configurationValue (observed : LogAttempt configurationValue) error files →
    LogAttempt.outcome observed ≡ LogAt.failed {configurationValue} error files →
    Step (logging configurationValue) (logCompleted configurationValue observed) (blocked error)
  completed : ∀ configurationValue delay → Step (reviewing configurationValue) (batchFinished delay) (waiting delay)
  retryBlocked : ∀ error → Step (blocked error) retry reading
  retryWaiting : ∀ delay → Step (waiting delay) retry reading

reviewRequiresLog : ∀ before event configurationValue → Step before event (reviewing configurationValue) →
  before ≡ logging configurationValue
reviewRequiresLog .(logging configurationValue) .(logCompleted configurationValue observed) configurationValue
  (ready .configurationValue observed files saved) = refl

logSuccessExact : ∀ configurationValue (observed : LogAttempt configurationValue) files →
  LogAttempt.outcome observed ≡ LogAt.written {configurationValue} files →
  Σ Log.State
    (λ before → files ≡ Log.append (LogAttempt.entry observed) before)
logSuccessExact configurationValue observed files saved
  with LogAt.writtenRequiresReceipts configurationValue
    (LogAttempt.entry observed) (LogAttempt.events observed) files
    (subst (LogAt.Attempt configurationValue (LogAttempt.entry observed) (LogAttempt.events observed))
      saved (LogAttempt.completed observed))
... | handle , before , exactEvents , exactContents = before , exactContents

failedLogCannotReview : ∀ configurationValue (observed : LogAttempt configurationValue) error files →
  LogAttempt.outcome observed ≡ LogAt.failed {configurationValue} error files →
  ∀ next → Step (logging configurationValue) (logCompleted configurationValue observed) (reviewing next) → ⊥
failedLogCannotReview configurationValue observed error files failure next
  (ready .configurationValue .observed savedFiles saved) with trans (sym saved) failure
... | ()

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
