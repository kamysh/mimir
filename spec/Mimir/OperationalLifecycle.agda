{-# OPTIONS --safe #-}
-- Configuration compatibility is checked before database/model work.
-- Log failure degrades logging and is reported; it cannot forbid reviews.
-- A successful batch proceeds immediately, without an invented delay.
module Mimir.OperationalLifecycle where

open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Mimir.Text using (Text)
import Mimir.OperationalConfiguration as C
import Mimir.ConfigurationSchema as Schema
import Mimir.OperationalLogProtocol as Logging

logs : Schema.Config → C.Logging
logs configurationValue = C.Settings.logs (C.Admitted.value (Schema.Config.operations configurationValue))

module LogAt (configurationValue : Schema.Config) =
  Logging.For (C.Logging.directory (logs configurationValue))

record LogAttempt (configurationValue : Schema.Config) : Set where
  field
    entry : List Logging.Byte
    events : List (LogAt.Event configurationValue)
    outcome : LogAt.Outcome configurationValue
    completed : LogAt.Attempt configurationValue entry events outcome

data State : Set where
  reading : State
  logging reviewing : Schema.Config → State
  blocked : Text → State

data Event : Set where
  configuration : Text ⊎ Schema.Config → Event
  logCompleted : ∀ configurationValue → LogAttempt configurationValue → Event
  batchFinished retry : Event

data Step : State → Event → State → Set where
  compatible : ∀ configurationValue → Step reading (configuration (inj₂ configurationValue)) (logging configurationValue)
  rejected : ∀ error → Step reading (configuration (inj₁ error)) (blocked error)
  ready : ∀ configurationValue (observed : LogAttempt configurationValue) files →
    LogAttempt.outcome observed ≡ LogAt.written {configurationValue} files →
    Step (logging configurationValue) (logCompleted configurationValue observed) (reviewing configurationValue)
  degraded : ∀ configurationValue (observed : LogAttempt configurationValue) error files →
    LogAttempt.outcome observed ≡ LogAt.failed {configurationValue} error files →
    Step (logging configurationValue) (logCompleted configurationValue observed) (reviewing configurationValue)
  completed : ∀ configurationValue → Step (reviewing configurationValue) batchFinished reading
  retryBlocked : ∀ error → Step (blocked error) retry reading

reviewRequiresLog : ∀ before event configurationValue → Step before event (reviewing configurationValue) →
  before ≡ logging configurationValue
reviewRequiresLog _ _ _ (ready _ _ _ _) = refl
reviewRequiresLog _ _ _ (degraded _ _ _ _ _) = refl

logSuccessExact : ∀ configurationValue (observed : LogAttempt configurationValue) files →
  LogAttempt.outcome observed ≡ LogAt.written {configurationValue} files →
  Σ Logging.Contents (λ before → files ≡ before Data.List.++ LogAttempt.entry observed)
logSuccessExact configurationValue observed files saved =
  LogAt.completeEntryRetained configurationValue (LogAttempt.entry observed) (LogAttempt.events observed) files
    (subst (LogAt.Attempt configurationValue (LogAttempt.entry observed) (LogAttempt.events observed))
      saved (LogAttempt.completed observed))

failedLogStillReviews : ∀ configurationValue observed error files →
  LogAttempt.outcome observed ≡ LogAt.failed {configurationValue} error files →
  Step (logging configurationValue) (logCompleted configurationValue observed) (reviewing configurationValue)
failedLogStillReviews = degraded

reviewRequiresCompatible : ∀ before event configurationValue → Step before event (reviewing configurationValue) →
  C.Settings.version (C.Admitted.value (Schema.Config.operations configurationValue)) ≡ C.formatVersion
reviewRequiresCompatible before event configurationValue step = C.acceptedVersion (Schema.Config.operations configurationValue)

retryRevalidates : ∀ error after → Step (blocked error) retry after → after ≡ reading
retryRevalidates error .reading (retryBlocked .error) = refl

completedBatchContinues : ∀ configurationValue after → Step (reviewing configurationValue) batchFinished after → after ≡ reading
completedBatchContinues configurationValue .reading (completed .configurationValue) = refl
