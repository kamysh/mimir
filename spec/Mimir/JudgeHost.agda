{-# OPTIONS --safe #-}
-- CLI/watch policy around the existing review controller. Model claims are
-- never accepted as reports here: the runner/receipt composition produces the
-- report, then this module derives process status and watch behavior from it.
module Mimir.JudgeHost where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≟_; _≤?_; _⊔_; _⊓_)
open import Data.String using (toList)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (does; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.Judge as Judge
import Mimir.JudgeStateRecords as Records
import Mimir.Effects as Effects
import Mimir.ConfigurationValues as Values

module State = Records.Over ℕ

data Exit : Set where success invalidConfig incomplete alreadyRunning unavailable : Exit

code : Exit → ℕ
code success = 0
code invalidConfig = 2
code incomplete = 3
code alreadyRunning = 4
code unavailable = 5

record Outcome : Set where
  constructor outcome
  field exit : Exit; degraded idle : Bool

is : Text → Text → Bool
is actual expected = does (actual ≟Text expected)

isDeferred : State.Report → Bool
isDeferred report with State.Report.blockReason report
... | nothing = false
... | just reason = is reason (toList "review_deferred")

reportExit : State.Report → Exit
reportExit report with is status (toList "idle") ∨ is status (toList "complete")
  where status = State.Report.status report
... | true = success
... | false with is (State.Report.status report) (toList "partial") ∨ is (State.Report.status report) (toList "blocked")
...   | true = incomplete
...   | false = unavailable

outcomeOf : Bool → State.Report → Outcome
outcomeOf watch report = outcome exit degraded (is status (toList "idle"))
  where
  status = State.Report.status report
  degraded = is status (toList "blocked") ∨ is status (toList "partial")
  exit : Exit
  exit with watch ∧ isDeferred report
  ... | true = success
  ... | false = reportExit report

record Watch : Set where
  constructor watchState
  field episode digestProblem : Bool

data Transition : Set where
  invalidConfiguration lockBusy stateUnavailable incompleteRun recovered
    digestUnavailable digestAvailable : Transition

failureMessage : Exit → Transition
failureMessage invalidConfig = invalidConfiguration
failureMessage alreadyRunning = lockBusy
failureMessage unavailable = stateUnavailable
failureMessage _ = incompleteRun

episodeMessage : Watch → Outcome → Maybe Transition
episodeMessage state result with Outcome.degraded result | Watch.episode state
... | true | false = just (failureMessage (Outcome.exit result))
... | true | true = nothing
... | false | false = nothing
... | false | true with Outcome.idle result
...   | true = just recovered
...   | false = nothing

advance : Watch → Outcome → Watch
advance state result = watchState episode (Watch.digestProblem state)
  where
  episode : Bool
  episode with Outcome.degraded result | Outcome.idle result
  ... | true | _ = true
  ... | false | true = false
  ... | false | false = Watch.episode state

-- This startup protocol must finish before the first batch can read the
-- queue. Both connection and LISTEN acknowledgement are native observations;
-- there is no timer, fabricated success, or queue read in this protocol.
module Subscription where
  data Effect : Set where
    connect : Values.Database → Effect
    listen : ℕ → Effect

  Reply : Effect → Set
  Reply (connect dbConfig) = Text ⊎ ℕ
  Reply (listen handle) = Text ⊎ ⊤

  module E = Effects.Protocol Effect Reply
  open E public

  start : Values.Database → Script (Text ⊎ ℕ)
  start dbConfig = ask (connect dbConfig) λ where
    (inj₁ error) → done (inj₁ error)
    (inj₂ handle) → ask (listen handle) λ where
      (inj₁ error) → done (inj₁ error)
      (inj₂ tt) → done (inj₂ handle)

  successRequiresAcknowledgedListen : ∀ dbConfig events handle → Runs (start dbConfig) events (inj₂ handle) →
    events ≡ ((connect dbConfig , inj₂ handle) ∷ (listen handle , inj₂ tt) ∷ [])
  successRequiresAcknowledgedListen dbConfig events handle (replied _ _ (inj₁ error) ())
  successRequiresAcknowledgedListen dbConfig events handle (replied _ _ (inj₂ connected)
    (replied _ _ (inj₁ error) ()))
  successRequiresAcknowledgedListen dbConfig events handle (replied _ _ (inj₂ .handle)
    (replied _ _ (inj₂ tt) (returned .(inj₂ handle)))) = refl

data QueueWake : Set where workAvailable configurationChanged disconnected explicitRetry interrupted : QueueWake

data PrerequisiteWake : Set where configurationCorrected retryRequested stopped : PrerequisiteWake

data Phase : Set where
  subscribing : Watch → Phase
  waitingConfiguration : Watch → Phase
  running : Watch → Phase
  digest : Watch → Outcome → Phase
  continuing : Watch → List Transition → Phase
  awaitingWork : Watch → List Transition → Phase
  waitingPrerequisite : Watch → List Transition → Phase
  exited : Exit → Phase

Reply : Phase → Set
Reply (subscribing state) = Exit ⊎ Outcome
Reply (waitingConfiguration state) = PrerequisiteWake
Reply (running state) = Outcome
Reply (digest state result) = Text ⊎ Bool -- error is an unavailable digest
Reply (continuing state messages) = ⊤ -- emit transitions, then continue; no timer
Reply (awaitingWork state messages) = QueueWake
Reply (waitingPrerequisite state messages) = PrerequisiteWake
Reply (exited code) = ⊤

digestTransitions : Bool → Bool → List Transition
digestTransitions false false = []
digestTransitions true true = []
digestTransitions false true = digestUnavailable ∷ []
digestTransitions true false = digestAvailable ∷ []

completedWork : Outcome → Bool
completedWork (outcome success false false) = true
completedWork _ = false

schedule : Outcome → Watch → List Transition → Phase
schedule (outcome success false false) state messages = continuing state messages
schedule (outcome success false true) state messages = awaitingWork state messages
schedule _ state messages = waitingPrerequisite state messages

afterDigest : Watch → Outcome → Bool → Phase
afterDigest before result problem =
  schedule result after messages
  where
  after = record (advance before result) { digestProblem = problem }
  messages : List Transition
  messages with episodeMessage before result
  ... | nothing = digestTransitions (Watch.digestProblem before) problem
  ... | just transition = digestTransitions (Watch.digestProblem before) problem Data.List.++ (transition ∷ [])

step : (phase : Phase) → Reply phase → Phase
step (subscribing state) (inj₁ invalidConfig) = waitingConfiguration state
step (subscribing state) (inj₁ code) = waitingPrerequisite state (failureMessage code ∷ [])
step (subscribing state) (inj₂ result) = digest state result
step (waitingConfiguration state) configurationCorrected = subscribing state
step (waitingConfiguration state) retryRequested = subscribing state
step (waitingConfiguration state) stopped = exited success
step (running state) result = digest state result
step (digest state result) (inj₁ error) = afterDigest state result true
step (digest state result) (inj₂ problem) = afterDigest state result problem
step (continuing state messages) reply = running state
step (awaitingWork state messages) workAvailable = running state
step (awaitingWork state messages) configurationChanged = subscribing state
step (awaitingWork state messages) disconnected = subscribing state
step (awaitingWork state messages) explicitRetry = subscribing state
step (awaitingWork state messages) interrupted = exited success
step (waitingPrerequisite state messages) configurationCorrected = subscribing state
step (waitingPrerequisite state messages) retryRequested = subscribing state
step (waitingPrerequisite state messages) stopped = exited success
step (exited code) reply = exited code

startWatch : Phase
startWatch = subscribing (watchState false false)

cancelAtWait : ∀ state messages →
  step (waitingPrerequisite state messages) stopped ≡ exited success
cancelAtWait state messages = refl

successfulBatchDoesNotCloseEpisode : ∀ episode digestProblem →
  Watch.episode (advance (watchState episode digestProblem) (outcome success false false)) ≡ episode
successfulBatchDoesNotCloseEpisode episode digestProblem = refl

data Immediate : Phase → Set where
  ready : ∀ state messages → Immediate (continuing state messages)

successfulBatchContinuesImmediately : ∀ before reply →
  Immediate (step (digest before (outcome success false false)) reply)
successfulBatchContinuesImmediately before (inj₁ error) = ready _ _
successfulBatchContinuesImmediately before (inj₂ problem) = ready _ _

data AwaitsWork : Phase → Set where
  subscribed : ∀ state messages → AwaitsWork (awaitingWork state messages)

idleBatchWaitsForWork : ∀ before reply →
  AwaitsWork (step (digest before (outcome success false true)) reply)
idleBatchWaitsForWork before (inj₁ error) = subscribed _ _
idleBatchWaitsForWork before (inj₂ problem) = subscribed _ _

cancelAtWorkWait : ∀ state messages →
  step (awaitingWork state messages) interrupted ≡ exited success
cancelAtWorkWait state messages = refl

disconnectionRequiresSubscription : ∀ state messages →
  step (awaitingWork state messages) disconnected ≡ subscribing state
disconnectionRequiresSubscription state messages = refl

configurationChangeRequiresSubscription : ∀ state messages →
  step (awaitingWork state messages) configurationChanged ≡ subscribing state
configurationChangeRequiresSubscription state messages = refl

retryRequiresSubscription : ∀ state messages →
  step (waitingPrerequisite state messages) retryRequested ≡ subscribing state
retryRequiresSubscription state messages = refl
