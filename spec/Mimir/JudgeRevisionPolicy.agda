{-# OPTIONS --safe #-}
-- Candidate-conflict retry and deferral policy around the budgeted controller.
-- This policy never manufactures a confirmed receipt. A successful tool call
-- stops the local revision loop only after an authoritative read is nonpending;
-- the later batch read still decides confirmed/corrected/unavailable counts.
module Mimir.JudgeRevisionPolicy where

open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤?_; _<?_)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.Judge as Judge
import Mimir.ReviewObservation as Observation

record State : Set where
  constructor mkState
  field conflicts : ℕ; lastConflict lastRejection : Maybe Text; settled failed : Bool

initial : State
initial = mkState 0 nothing nothing false false

data Event : Set where
  candidateConflict inputRejected : Text → Event
  modelBudgetExhausted modelError modelTimeout toolBudgetExhausted : Event
  malformedCallWithoutToolBudget toolInfrastructureError : Event
  modelDone : Event
  reviewed : Judge.Completion.Receipt → Event

data Action : Set where retryCandidate retryInput continueRevision endRevision failBatch : Action

record Step : Set where
  constructor mkStep
  field state : State; action : Action

conditionalFailure : State → Step
conditionalFailure state with State.conflicts state
... | zero = mkStep (record state { failed = true }) failBatch
... | suc _ = mkStep state endRevision

step : State → Event → Step
step state (candidateConflict detail) with suc (State.conflicts state) ≤? 1
... | Relation.Nullary.yes _ = mkStep
  (record state { conflicts = suc (State.conflicts state) ; lastConflict = just detail }) retryCandidate
... | Relation.Nullary.no _ = mkStep
  (record state { conflicts = suc (State.conflicts state) ; lastConflict = just detail }) endRevision
step state (inputRejected detail) = mkStep (record state { lastRejection = just detail }) retryInput
step state modelBudgetExhausted = conditionalFailure state
step state modelError = conditionalFailure state
step state modelTimeout = conditionalFailure state
step state toolBudgetExhausted = conditionalFailure state
step state malformedCallWithoutToolBudget = mkStep (record state { failed = true }) failBatch
step state toolInfrastructureError = mkStep (record state { failed = true }) failBatch
step state modelDone = mkStep state endRevision
step state (reviewed Judge.Completion.pending) = mkStep state continueRevision
step state (reviewed Judge.Completion.confirmed) = mkStep (record state { settled = true }) endRevision
step state (reviewed Judge.Completion.corrected) = mkStep (record state { settled = true }) endRevision
step state (reviewed Judge.Completion.unavailable) = mkStep (record state { settled = true }) endRevision

shouldDefer : State → Bool
shouldDefer state = does (0 <? State.conflicts state) ∧ not (State.settled state) ∧ not (State.failed state)

data Deferral : Set where
  tooManyDeferred : Deferral
  retained : List Observation.Deferred → Deferral

finish : Observation.Pin → State → List Observation.Deferred → Deferral
finish pin state deferred with shouldDefer state
... | false = retained deferred
... | true with length deferred <? 1000
...   | Relation.Nullary.no _ = tooManyDeferred
...   | Relation.Nullary.yes _ = retained (deferred ++
  (Observation.deferred (Observation.Pin.identity pin) (Observation.Pin.sourceRevision pin) ∷ []))

inputRejectionNotCandidateConflict : ∀ state detail →
  State.conflicts (Step.state (step state (inputRejected detail))) ≡ State.conflicts state
inputRejectionNotCandidateConflict state detail = refl

doneDoesNotSettle : ∀ state → State.settled (Step.state (step state modelDone)) ≡ State.settled state
doneDoesNotSettle state = refl
