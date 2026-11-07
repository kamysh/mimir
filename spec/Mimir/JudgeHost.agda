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
  field failures : ℕ; episode digestProblem : Bool

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

advance : ℕ → Watch → Outcome → Watch
advance usizeMaximum state result = watchState failures episode (Watch.digestProblem state)
  where
  failures : ℕ
  failures with Outcome.exit result
  ... | success = 0
  ... | _ = suc (Watch.failures state) ⊓ usizeMaximum
  episode : Bool
  episode with Outcome.degraded result | Outcome.idle result
  ... | true | _ = true
  ... | false | true = false
  ... | false | false = Watch.episode state

delay : ℕ → ℕ → Watch → ℕ
delay interval threshold state = Judge.Watch.retryDelay threshold (Watch.failures state) interval (interval ⊔ 3600)

admitted : ℕ → ℕ → Bool
admitted interval threshold = does (1 ≤? interval) ∧ does (1 ≤? threshold)

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

data QueueWake : Set where workAvailable disconnected interrupted : QueueWake

data Phase : Set where
  subscribing : Watch → Phase
  running : Watch → Phase
  digest : Watch → Outcome → Phase
  continuing : Watch → List Transition → Phase
  awaitingWork : Watch → List Transition → Phase
  waiting : Watch → ℕ → List Transition → Phase
  exited : Exit → Phase

Reply : Phase → Set
Reply (subscribing state) = Exit ⊎ Outcome
Reply (running state) = Outcome
Reply (digest state result) = Text ⊎ Bool -- error is an unavailable digest
Reply (continuing state messages) = ⊤ -- emit transitions, then continue; no timer
Reply (awaitingWork state messages) = QueueWake
Reply (waiting state seconds messages) = Bool -- true = Ctrl-C, false = timer
Reply (exited code) = ⊤

digestTransitions : Bool → Bool → List Transition
digestTransitions false false = []
digestTransitions true true = []
digestTransitions false true = digestUnavailable ∷ []
digestTransitions true false = digestAvailable ∷ []

completedWork : Outcome → Bool
completedWork (outcome success false false) = true
completedWork _ = false

schedule : Outcome → Watch → ℕ → List Transition → Phase
schedule (outcome success false false) state seconds messages = continuing state messages
schedule (outcome success false true) state seconds messages = awaitingWork state messages
schedule _ state seconds messages = waiting state seconds messages

afterDigest : ℕ → ℕ → ℕ → Watch → Outcome → Bool → Phase
afterDigest usizeMaximum interval threshold before result problem =
  schedule result after (delay interval threshold after) messages
  where
  after = record (advance usizeMaximum before result) { digestProblem = problem }
  messages : List Transition
  messages with episodeMessage before result
  ... | nothing = digestTransitions (Watch.digestProblem before) problem
  ... | just transition = digestTransitions (Watch.digestProblem before) problem Data.List.++ (transition ∷ [])

step : ℕ → ℕ → ℕ → (phase : Phase) → Reply phase → Phase
step usizeMaximum interval threshold (subscribing state) (inj₁ code) = exited code
step usizeMaximum interval threshold (subscribing state) (inj₂ result) = digest state result
step usizeMaximum interval threshold (running state) result = digest state result
step usizeMaximum interval threshold (digest state result) (inj₁ error) = afterDigest usizeMaximum interval threshold state result true
step usizeMaximum interval threshold (digest state result) (inj₂ problem) = afterDigest usizeMaximum interval threshold state result problem
step usizeMaximum interval threshold (continuing state messages) reply = running state
step usizeMaximum interval threshold (awaitingWork state messages) workAvailable = running state
step usizeMaximum interval threshold (awaitingWork state messages) disconnected = subscribing state
step usizeMaximum interval threshold (awaitingWork state messages) interrupted = exited success
step usizeMaximum interval threshold (waiting state seconds messages) true = exited success
step usizeMaximum interval threshold (waiting state seconds messages) false = running state
step usizeMaximum interval threshold (exited code) reply = exited code

startWatch : ℕ → ℕ → Phase
startWatch interval threshold with admitted interval threshold
... | false = exited invalidConfig
... | true = subscribing (watchState 0 false false)

cancelAtWait : ∀ maximum interval threshold state seconds messages →
  step maximum interval threshold (waiting state seconds messages) true ≡ exited success
cancelAtWait maximum interval threshold state seconds messages = refl

successfulBatchDoesNotCloseEpisode : ∀ maximum failures episode digestProblem →
  Watch.episode (advance maximum (watchState failures episode digestProblem) (outcome success false false)) ≡ episode
successfulBatchDoesNotCloseEpisode maximum failures episode digestProblem = refl

-- A confirmed non-idle batch cannot require any timer acknowledgement,
-- independently of the configured interval, failure history or digest reply.
data Immediate : Phase → Set where
  ready : ∀ state messages → Immediate (continuing state messages)

successfulBatchContinuesImmediately : ∀ maximum interval threshold before reply →
  Immediate (step maximum interval threshold
    (digest before (outcome success false false)) reply)
successfulBatchContinuesImmediately maximum interval threshold before (inj₁ error) = ready _ _
successfulBatchContinuesImmediately maximum interval threshold before (inj₂ problem) = ready _ _

data AwaitsWork : Phase → Set where
  subscribed : ∀ state messages → AwaitsWork (awaitingWork state messages)

idleBatchWaitsForWork : ∀ maximum interval threshold before reply →
  AwaitsWork (step maximum interval threshold (digest before (outcome success false true)) reply)
idleBatchWaitsForWork maximum interval threshold before (inj₁ error) = subscribed _ _
idleBatchWaitsForWork maximum interval threshold before (inj₂ problem) = subscribed _ _

cancelAtWorkWait : ∀ maximum interval threshold state messages →
  step maximum interval threshold (awaitingWork state messages) interrupted ≡ exited success
cancelAtWorkWait maximum interval threshold state messages = refl

-- A lost connection never resumes the queue wait directly. The shared
-- subscribing phase requires acknowledgement and a fresh first batch.
disconnectionRequiresSubscription : ∀ maximum interval threshold state messages →
  step maximum interval threshold (awaitingWork state messages) disconnected ≡ subscribing state
disconnectionRequiresSubscription maximum interval threshold state messages = refl
