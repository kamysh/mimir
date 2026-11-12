{-# OPTIONS --safe #-}
-- Recovery is stated over the world affected by the existing effect protocol.
module Mimir.Recovery
  (World Effect Result : Set)
  (ObservationIndex : World → Set)
  (Reply : Effect → Set)
  (Atomic : World → (effect : Effect) → Reply effect → World → Set)
  (Crash : World → World → Set)
  (Observation : (initial : World) → ObservationIndex initial → Set)
  (observe : (initial : World) → (index : ObservationIndex initial) → World → Observation initial index)
  (finish : Result → World → World)
  (Succeeded : Result → Set)
  (Integrity : World → Set) where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
import Mimir.Effects as Effects

module E = Effects.Protocol Effect Reply
open E using (Script; done; ask; Event; Prefix)

-- An interruption occurs while an operation still has an effect to perform.
-- Once it has returned, its result has been received and it is complete.
data Interrupted : Script Result → World → World → Set where
  stopped : ∀ {effect next before after} → Crash before after → Interrupted (ask effect next) before after
  replied : ∀ {effect next reply before middle after} →
    Atomic before effect reply middle → Interrupted (next reply) middle after →
    Interrupted (ask effect next) before after

-- These are the operation's existing unsuccessful results, not new errors.
-- Returning an error does not publish a successful result into the world.
-- Any durable change before that return is still accounted for by Atomic.
data Failed : Script Result → World → World → Set where
  failedReturn : ∀ {result world} → ¬ Succeeded result →
    Failed (done result) world world
  failedReply : ∀ {effect next reply before middle after} →
    Atomic before effect reply middle → Failed (next reply) middle after →
    Failed (ask effect next) before after

data Attempts* (program : Script Result) : World → World → Set where
  noAttempts : ∀ {world} → Attempts* program world world
  afterInterruption : ∀ {before middle after} →
    Interrupted program before middle → Attempts* program middle after → Attempts* program before after
  afterFailure : ∀ {before middle after} →
    Failed program before middle → Attempts* program middle after → Attempts* program before after

data Completed : Script Result → World → World → Set where
  returned : ∀ {result world} → Succeeded result → Completed (done result) world (finish result world)
  replied : ∀ {effect next reply before middle after} →
    Atomic before effect reply middle → Completed (next reply) middle after →
    Completed (ask effect next) before after

data Applied : List Event → World → World → Set where
  noEffects : ∀ {world} → Applied [] world world
  appliedEffect : ∀ {effect reply events before middle after} →
    Atomic before effect reply middle → Applied events middle after →
    Applied ((effect , reply) ∷ events) before after

completedTrace : ∀ {program before after} → Completed program before after →
  Σ (List Event) (λ events → Σ Result (λ result → Σ World (λ middle →
    E.Runs program events result × Succeeded result × Applied events before middle × after ≡ finish result middle)))
completedTrace (returned {result = result} {world = world} success) =
  [] , result , world , E.returned result , success , noEffects , refl
completedTrace (replied {effect = effect} {next = next} {reply = reply} atomic rest)
  with completedTrace rest
... | events , result , middle , execution , success , effects , finalized =
  ((effect , reply) ∷ events) , result , middle , E.replied effect next reply execution ,
  success , appliedEffect atomic effects , finalized

-- Transition systems allow the existing unbounded read protocols to use the
-- same recovery gate as finite scripts. No traversal fuel is introduced.
data Next (State : Set) : Set where
  returned : Result → Next State
  perform : (effect : Effect) → (Reply effect → State) → Next State

record Machine : Set₁ where
  field
    State : Set
    next : State → Next State

module MachineRuns (machine : Machine) where
  open Machine machine

  data StoppedRun : State → World → World → Set where
    interrupted : ∀ {state effect continuation before after} →
      next state ≡ Next.perform effect continuation → Crash before after → StoppedRun state before after
    replied : ∀ {state effect continuation reply before middle after} →
      next state ≡ Next.perform effect continuation → Atomic before effect reply middle →
      StoppedRun (continuation reply) middle after → StoppedRun state before after

  data FailedRun : State → World → World → Set where
    failed : ∀ {state result world} → next state ≡ Next.returned result → ¬ Succeeded result → FailedRun state world world
    replied : ∀ {state effect continuation reply before middle after} →
      next state ≡ Next.perform effect continuation → Atomic before effect reply middle →
      FailedRun (continuation reply) middle after → FailedRun state before after

  data CompletedRun : State → World → World → Set where
    returned : ∀ {state result world} → next state ≡ Next.returned result → Succeeded result →
      CompletedRun state world (finish result world)
    replied : ∀ {state effect continuation reply before middle after} →
      next state ≡ Next.perform effect continuation → Atomic before effect reply middle →
      CompletedRun (continuation reply) middle after → CompletedRun state before after

  data AttemptedRuns (initial : State) : World → World → Set where
    none : ∀ {world} → AttemptedRuns initial world world
    interrupted : ∀ {before middle after} → StoppedRun initial before middle →
      AttemptedRuns initial middle after → AttemptedRuns initial before after
    failed : ∀ {before middle after} → FailedRun initial before middle →
      AttemptedRuns initial middle after → AttemptedRuns initial before after

  data MachinePrefix : State → List Event → State → Set where
    stopped : ∀ state → MachinePrefix state [] state
    replied : ∀ {state effect continuation reply events final} → next state ≡ Next.perform effect continuation →
      MachinePrefix (continuation reply) events final → MachinePrefix state ((effect , reply) ∷ events) final

  appendPrefix : ∀ {start middle final first second} → MachinePrefix start first middle →
    MachinePrefix middle second final → MachinePrefix start (first ++ second) final
  appendPrefix (stopped state) second = second
  appendPrefix (replied step rest) second = replied step (appendPrefix rest second)

scriptStep : Script Result → Next (Script Result)
scriptStep (done result) = Next.returned result
scriptStep (ask effect continuation) = Next.perform effect continuation

scriptMachine : Machine
scriptMachine = record { State = Script Result ; next = scriptStep }

module Finite = MachineRuns scriptMachine

finiteInterruption : ∀ {program before after} → Finite.StoppedRun program before after → Interrupted program before after
finiteInterruption {done result} (Finite.interrupted () crash)
finiteInterruption {ask effect continuation} (Finite.interrupted refl crash) = stopped crash
finiteInterruption {done result} (Finite.replied () atomic rest)
finiteInterruption {ask effect continuation} (Finite.replied refl atomic rest) = replied atomic (finiteInterruption rest)

finiteFailure : ∀ {program before after} → Finite.FailedRun program before after → Failed program before after
finiteFailure {done result} (Finite.failed refl notSuccessful) = failedReturn notSuccessful
finiteFailure {ask effect continuation} (Finite.failed () notSuccessful)
finiteFailure {done result} (Finite.replied () atomic rest)
finiteFailure {ask effect continuation} (Finite.replied refl atomic rest) = failedReply atomic (finiteFailure rest)

finiteCompletion : ∀ {program before after} → Finite.CompletedRun program before after → Completed program before after
finiteCompletion {done result} (Finite.returned refl succeeded) = returned succeeded
finiteCompletion {ask effect continuation} (Finite.returned () succeeded)
finiteCompletion {done result} (Finite.replied () atomic rest)
finiteCompletion {ask effect continuation} (Finite.replied refl atomic rest) = replied atomic (finiteCompletion rest)

finiteAttempts : ∀ {program before after} → Finite.AttemptedRuns program before after → Attempts* program before after
finiteAttempts Finite.none = noAttempts
finiteAttempts (Finite.interrupted first rest) = afterInterruption (finiteInterruption first) (finiteAttempts rest)
finiteAttempts (Finite.failed first rest) = afterFailure (finiteFailure first) (finiteAttempts rest)

record ScriptRecovery (Input : Set) : Set₁ where
  field
    -- A pure expected observation also describes generative operations: the
    -- business result is specified without choosing PostgreSQL's future UUID.
    expected : (input : Input) → (initial : World) → (index : ObservationIndex initial) → Observation initial index
    script : Input → Script Result
  Goal : Input → World → World → Set
  Goal input before after = ∀ index → observe before index after ≡ expected input before index
  field
    converges : ∀ input before interrupted final →
      Attempts* (script input) before interrupted →
      (completed : Completed (script input) interrupted final) →
      ∀ index → observe before index final ≡
        expected input before index
    rollbackInterrupted : ∀ input before after → Interrupted (script input) before after → after ≡ before
    rollbackFailed : ∀ input before after → Failed (script input) before after → after ≡ before

record Recoverable (Input : Set) : Set₁ where
  field
    machine : Machine
    initial : Input → Machine.State machine
    expected : (input : Input) → (before : World) → (index : ObservationIndex before) → Observation before index
  module Runs = MachineRuns machine
  Goal : Input → World → World → Set
  Goal input before after = ∀ index → observe before index after ≡ expected input before index
  field
    converges : ∀ input before middle after → Runs.AttemptedRuns (initial input) before middle →
      Runs.CompletedRun (initial input) middle after → Goal input before after
    rollbackInterrupted : ∀ input before after → Runs.StoppedRun (initial input) before after → after ≡ before
    rollbackFailed : ∀ input before after → Runs.FailedRun (initial input) before after → after ≡ before

  -- Every unsuccessful attempt restores the original business state.
  -- A new attempt therefore starts afresh; it consumes no saved progress.
  restartsFresh : ∀ input before after → Runs.AttemptedRuns (initial input) before after → after ≡ before
  restartsFresh input before .before Runs.none = refl
  restartsFresh input before after (Runs.interrupted {middle = middle} first rest) =
    trans (restartsFresh input middle after rest) (rollbackInterrupted input before middle first)
  restartsFresh input before after (Runs.failed {middle = middle} first rest) =
    trans (restartsFresh input middle after rest) (rollbackFailed input before middle first)

fromScript : ∀ {Input} → ScriptRecovery Input → Recoverable Input
fromScript certified = record
  { machine = scriptMachine
  ; initial = ScriptRecovery.script certified
  ; expected = ScriptRecovery.expected certified
  ; converges = λ input before middle after attempts completed →
      ScriptRecovery.converges certified input before middle after (finiteAttempts attempts) (finiteCompletion completed)
  ; rollbackInterrupted = λ input before after attempt →
      ScriptRecovery.rollbackInterrupted certified input before after (finiteInterruption attempt)
  ; rollbackFailed = λ input before after attempt →
      ScriptRecovery.rollbackFailed certified input before after (finiteFailure attempt)
  }

module ReadOnlyMachine (machine : Machine)
  (unchangedEffect : ∀ before effect reply after → Atomic before effect reply after → after ≡ before)
  (unchangedCrash : ∀ before after → Crash before after → after ≡ before)
  (unchangedFinish : ∀ result world → finish result world ≡ world) where
  module M = MachineRuns machine

  interruptedUnchanged : ∀ {state before after} → M.StoppedRun state before after → after ≡ before
  interruptedUnchanged (M.interrupted ready crash) = unchangedCrash _ _ crash
  interruptedUnchanged (M.replied ready atomic rest) =
    trans (interruptedUnchanged rest) (unchangedEffect _ _ _ _ atomic)

  failedUnchanged : ∀ {state before after} → M.FailedRun state before after → after ≡ before
  failedUnchanged (M.failed ready notSuccessful) = refl
  failedUnchanged (M.replied ready atomic rest) =
    trans (failedUnchanged rest) (unchangedEffect _ _ _ _ atomic)

  completedUnchanged : ∀ {state before after} → M.CompletedRun state before after → after ≡ before
  completedUnchanged (M.returned {result = result} {world = world} ready succeeded) = unchangedFinish result world
  completedUnchanged (M.replied ready atomic rest) =
    trans (completedUnchanged rest) (unchangedEffect _ _ _ _ atomic)

  attemptsUnchanged : ∀ {state before after} → M.AttemptedRuns state before after → after ≡ before
  attemptsUnchanged M.none = refl
  attemptsUnchanged (M.interrupted first rest) = trans (attemptsUnchanged rest) (interruptedUnchanged first)
  attemptsUnchanged (M.failed first rest) = trans (attemptsUnchanged rest) (failedUnchanged first)

  readOnly : ∀ {Input} → (Input → Machine.State machine) → Recoverable Input
  readOnly initial = record
    { machine = machine
    ; initial = initial
    ; expected = λ _ world index → observe world index world
    ; converges = λ input before middle after attempts completed index →
        cong (observe before index) (trans (completedUnchanged completed) (attemptsUnchanged attempts))
    ; rollbackInterrupted = λ _ _ _ → interruptedUnchanged
    ; rollbackFailed = λ _ _ _ → failedUnchanged
    }

-- A pure result has no effects before its response is returned.
module Pure {Input : Set} (answer : Input → Result) where

  unchanged : ∀ input → Succeeded (answer input) → ∀ before after →
    Attempts* (done (answer input)) before after → after ≡ before
  unchanged input success before .before noAttempts = refl
  unchanged input success before after (afterInterruption () rest)
  unchanged input success before after (afterFailure (failedReturn failed) rest) = ⊥-elim (failed success)

  convergesPure : ∀ input before middle final →
    Attempts* (done (answer input)) before middle → Completed (done (answer input)) middle final →
    ∀ index → observe before index final ≡ observe before index (finish (answer input) before)
  convergesPure input before middle .(finish (answer input) middle) attempts (returned success) index =
    cong (λ world → observe before index (finish (answer input) world)) (unchanged input success before middle attempts)

  pure : Recoverable Input
  pure = fromScript record
    { expected = λ input world index → observe world index (finish (answer input) world)
    ; script = λ input → done (answer input)
    ; converges = convergesPure
    ; rollbackInterrupted = λ _ _ _ ()
    ; rollbackFailed = λ _ _ _ → λ { (failedReturn _) → refl }
    }
    where
    pureAttempts : ∀ input before after → Attempts* (done (answer input)) before after → after ≡ before
    pureAttempts input before .before noAttempts = refl
    pureAttempts input before after (afterInterruption () rest)
    pureAttempts input before after (afterFailure (failedReturn failed) rest) = pureAttempts input before after rest

-- A read-only family needs no per-query recovery machinery. Its existing
-- result specification remains authoritative; this proof concerns recovery.
module ReadOnly
  (unchangedEffect : ∀ before effect reply after → Atomic before effect reply after → after ≡ before)
  (unchangedCrash : ∀ before after → Crash before after → after ≡ before)
  (unchangedFinish : ∀ result world → finish result world ≡ world) where

  interruptedUnchanged : ∀ {program before after} → Interrupted program before after → after ≡ before
  interruptedUnchanged (stopped crash) = unchangedCrash _ _ crash
  interruptedUnchanged (replied atomic rest) =
    trans (interruptedUnchanged rest) (unchangedEffect _ _ _ _ atomic)

  failedUnchanged : ∀ {program before after} → Failed program before after → after ≡ before
  failedUnchanged (failedReturn failed) = refl
  failedUnchanged (failedReply atomic rest) =
    trans (failedUnchanged rest) (unchangedEffect _ _ _ _ atomic)

  attemptsUnchanged : ∀ {program before after} → Attempts* program before after → after ≡ before
  attemptsUnchanged noAttempts = refl
  attemptsUnchanged (afterInterruption first rest) =
    trans (attemptsUnchanged rest) (interruptedUnchanged first)
  attemptsUnchanged (afterFailure first rest) =
    trans (attemptsUnchanged rest) (failedUnchanged first)

  completedUnchanged : ∀ {program before after} → Completed program before after → after ≡ before
  completedUnchanged (returned {result = result} {world = world} succeeded) = unchangedFinish result world
  completedUnchanged (replied atomic rest) =
    trans (completedUnchanged rest) (unchangedEffect _ _ _ _ atomic)

  readOnly : ∀ {Input} → (Input → Script Result) → Recoverable Input
  readOnly program = fromScript record
    { expected = λ _ world index → observe world index world
    ; script = program
    ; converges = λ input before middle after attempts completed index →
        cong (observe before index) (trans (completedUnchanged completed) (attemptsUnchanged attempts))
    ; rollbackInterrupted = λ _ _ _ → interruptedUnchanged
    ; rollbackFailed = λ _ _ _ → failedUnchanged
    }

-- Under the agreed transaction boundary, a committed result is received and
-- complete. The attempts being retried are therefore precisely those which
-- left no durable change. This constructor also covers preparatory reads and
-- external work before that final transaction.
record AllOrNothing (Input : Set) : Set₁ where
  field
    expected : (input : Input) → (initial : World) → (index : ObservationIndex initial) → Observation initial index
    script : Input → Script Result
    interruptedUnchanged : ∀ input before after → Interrupted (script input) before after → after ≡ before
    failedUnchanged : ∀ input before after → Failed (script input) before after → after ≡ before
    achieves : ∀ input before after → Completed (script input) before after →
      ∀ index → observe before index after ≡ expected input before index

module Transactional {Input : Set} (one : AllOrNothing Input) where
  open AllOrNothing one

  attemptsUnchanged : ∀ input before after → Attempts* (script input) before after → after ≡ before
  attemptsUnchanged input before .before noAttempts = refl
  attemptsUnchanged input before after (afterInterruption {middle = middle} first rest) =
    trans (attemptsUnchanged input middle after rest) (interruptedUnchanged input before middle first)
  attemptsUnchanged input before after (afterFailure {middle = middle} first rest) =
    trans (attemptsUnchanged input middle after rest) (failedUnchanged input before middle first)

  convergesTransactional : ∀ input before middle after → Attempts* (script input) before middle →
    Completed (script input) middle after → ∀ index →
    observe before index after ≡ expected input before index
  convergesTransactional input before middle after attempts completed index
    with attemptsUnchanged input before middle attempts
  ... | refl = achieves input before after completed index

  transactional : Recoverable Input
  transactional = fromScript record
    { expected = expected
    ; script = script
    ; converges = convergesTransactional
    ; rollbackInterrupted = interruptedUnchanged
    ; rollbackFailed = failedUnchanged
    }

-- One final publication call. Failure leaves no durable change; success is
-- immediately returned. Its goal may describe a database-assigned identity
-- through the returned record rather than prescribing the identity's value.
record FinalCall (Input : Set) : Set₁ where
  field
    effect : Input → Effect
    answer : (input : Input) → Reply (effect input) → Result
    expected : (input : Input) → (before : World) → (index : ObservationIndex before) → Observation before index
    success : ∀ input before reply after → Atomic before (effect input) reply after →
      Succeeded (answer input reply) → ∀ index →
      observe before index (finish (answer input reply) after) ≡ expected input before index
    failureUnchanged : ∀ input before reply after → Atomic before (effect input) reply after →
      ¬ Succeeded (answer input reply) → after ≡ before
    crashUnchanged : ∀ before after → Crash before after → after ≡ before

module FinalPublication {Input : Set} (call : FinalCall Input) where
  open FinalCall call

  program : Input → Script Result
  program input = ask (effect input) (λ reply → done (answer input reply))

  interruptedUnchanged : ∀ input before after → Interrupted (program input) before after → after ≡ before
  interruptedUnchanged input before after (stopped crash) = crashUnchanged before after crash
  interruptedUnchanged input before after (replied atomic ())

  failedUnchanged : ∀ input before after → Failed (program input) before after → after ≡ before
  failedUnchanged input before after (failedReply {reply = reply} atomic (failedReturn notSuccessful)) =
    failureUnchanged input before reply after atomic notSuccessful

  atomicCall : AllOrNothing Input
  atomicCall = record
    { expected = expected
    ; script = program
    ; interruptedUnchanged = interruptedUnchanged
    ; failedUnchanged = failedUnchanged
    ; achieves = λ input before after → λ
        { (replied {reply = reply} atomic (returned succeeded)) → success input before reply _ atomic succeeded }
    }
  module Certified = Transactional atomicCall
  finalPublication : Recoverable Input
  finalPublication = Certified.transactional

-- Losing an optional feature must still deliver the essential observation.
-- This cannot be used for a prerequisite of the operation's core goal.
record Degradable {Input : Set} (operation : Recoverable Input)
  (Feature Core : Set) : Set₁ where
  open Recoverable operation
  field
    core : ∀ initial index → Observation initial index → Core
    without : Feature → Input → Script Result
    preservesCore : ∀ feature input before middle after →
      Runs.AttemptedRuns (initial input) before middle → Completed (without feature input) middle after →
      ∀ index → core before index (observe before index after) ≡
        core before index (expected input before index)

-- A fatal disposition is available only with evidence of a violated store
-- invariant. A retry remains tied to the operation's recovery certificate.
data Disposition {Input : Set} (operation : Recoverable Input)
  (Feature : Set) (world : World) : Set₁ where
  done : (result : Result) → Succeeded result → Disposition operation Feature world
  retry : Disposition operation Feature world
  degraded : ∀ {Core} → Degradable operation Feature Core → Feature → Disposition operation Feature world
  fatal : ¬ Integrity world → Disposition operation Feature world

data RunState {Input : Set} (operation : Recoverable Input) (input : Input) : Set where
  running : ∀ events (remaining : Machine.State (Recoverable.machine operation)) →
    MachineRuns.MachinePrefix (Recoverable.machine operation) (Recoverable.initial operation input) events remaining → RunState operation input

start : ∀ {Input} (operation : Recoverable Input) (input : Input) → RunState operation input
start operation input = running [] (Recoverable.initial operation input) (MachineRuns.stopped _)

advance : ∀ {Input} (operation : Recoverable Input) input events effect next
  {state : Machine.State (Recoverable.machine operation)} →
  MachineRuns.MachinePrefix (Recoverable.machine operation) (Recoverable.initial operation input) events state →
  Machine.next (Recoverable.machine operation) state ≡ Next.perform effect next →
  (reply : Reply effect) → RunState operation input
advance operation input events effect next prefix ready reply =
  running (events ++ ((effect , reply) ∷ [])) (next reply)
    (MachineRuns.appendPrefix (Recoverable.machine operation) prefix
      (MachineRuns.replied ready (MachineRuns.stopped _)))

-- The application supplies a total operation mapping for its closed request
-- type; this state cannot contain an uncertified script.
module Dispatcher (Request : Set) (Input : Request → Set)
  (operation : (request : Request) → Recoverable (Input request)) where
  data State : Set where
    running : (request : Request) → (input : Input request) →
      RunState (operation request) input → State

  begin : (request : Request) → (input : Input request) → State
  begin request input = running request input (start (operation request) input)

  restart : (request : Request) → (input : Input request) → State
  restart = begin
