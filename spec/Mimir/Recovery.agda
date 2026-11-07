{-# OPTIONS --safe #-}
-- The recovery goal is fixed here, outside operation implementations. Neither
-- an alternative predicate nor an operation-chosen observation is a field.
module Mimir.Recovery where

open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
import Mimir.ApplicationStore as Store
import Mimir.StructuredValue as Wire
import Mimir.Effects as Effects
import Mimir.DatabaseTransaction as Database

-- Assembly fixes World once for the entire dispatcher. An operation over a
-- smaller world cannot be supplied where this dispatcher expects the larger
-- one. The observation retains the WHOLE world and the complete semantic reply.
module Over (World : Set) where
  Observation = World × Wire.Value

  observe : World → Wire.Value → Observation
  observe state reply = state , reply

  record Intent (Input : Set) : Set where
    field
      intended : Input → World → World
      expectedReply : Input → World → Wire.Value

  record Invocation (Input : Set) : Set where
    constructor invocation
    field
      input : Input
      initial : World

  expected : ∀ {Input} → Intent Input → Invocation Input → Observation
  expected intent call = observe
    (Intent.intended intent (Invocation.input call) (Invocation.initial call))
    (Intent.expectedReply intent (Invocation.input call) (Invocation.initial call))

  Goal : ∀ {Input} → Intent Input → Invocation Input → World → Wire.Value → Set
  Goal intent call final reply = observe final reply ≡ expected intent call

  -- Both conclusions use the same original invocation. A retry cannot change
  -- either the starting world or its expected reply to make its result pass.
  goalDeterminesStateAndReply : ∀ {Input} (intent : Intent Input) call
    firstState firstReply secondState secondReply →
    Goal intent call firstState firstReply → Goal intent call secondState secondReply →
    firstState ≡ secondState × firstReply ≡ secondReply
  goalDeterminesStateAndReply intent call firstState firstReply secondState secondReply first second =
    cong proj₁ same , cong proj₂ same
    where same = trans first (sym second)

-- Concrete application operations share every represented store component:
-- graph and learning history, document chunks, BOTH vector tables and grounds.
-- This alias is chosen by application assembly, not by each operation.
module Business = Over Store.World

-- Atomic supplies the application's physical meaning for one effect and its
-- reply. A control transcript by itself is not a physical execution witness.
module Execution (World Effect : Set) (Reply : Effect → Set)
  (Atomic : World → (effect : Effect) → Reply effect → World → Set) where
  module E = Effects.Protocol Effect Reply

  data Changes : World → List E.Event → World → Set where
    unchanged : ∀ state → Changes state [] state
    changed : ∀ before effect reply middle {events after} →
      Atomic before effect reply middle → Changes middle events after →
      Changes before ((effect , reply) ∷ events) after

  record Completed {Result : Set} (script : E.Script Result)
    (before after : World) (result : Result) : Set where
    constructor completed
    field
      events : List E.Event
      returned : E.Runs script events result
      changes : Changes before events after

  data Interrupted {Result : Set} (script : E.Script Result)
    (before : World) : World → Set where
    -- Includes before the first effect, after any observed reply, and after
    -- the script finished but its caller did not receive the final result.
    atPrefix : ∀ events residual current → E.Prefix script events residual →
      Changes before events current → Interrupted script before current
    -- The active statement may have finished before its reply was delivered.
    -- Its physical change is retained; its reply is NOT an observed event.
    beforeReply : ∀ events effect continuation current reply after →
      E.Prefix script events (E.ask effect continuation) →
      Changes before events current → Atomic current effect reply after →
      Interrupted script before after

  private
    runPrefix : ∀ {Result} {script : E.Script Result} {events result} →
      E.Runs script events result → E.Prefix script events (E.done result)
    runPrefix (E.returned result) = E.stopped (E.done result)
    runPrefix (E.replied effect continuation reply rest) =
      E.replied effect continuation reply (runPrefix rest)

  completedRunMayLoseFinalReply : ∀ {Result} (script : E.Script Result)
    before after result → Completed script before after result →
    Interrupted script before after
  completedRunMayLoseFinalReply script before after result
    (completed events execution changes) =
    atPrefix events (E.done result) after (runPrefix execution) changes

-- Committed database statements use the existing PostgreSQL atomicity
-- dependency directly. No new rollback or acknowledgement assumptions appear.
module Transactions (World Statement : Set) (proposed : Statement → World → World) where
  Reply : Statement → Set
  Reply _ = Database.Receipt

  Atomic : World → Statement → Database.Receipt → World → Set
  Atomic before statement receipt after =
    Database.Atomic before (proposed statement before) receipt after

  module X = Execution World Statement Reply Atomic

  lostAcknowledgementIncludesBothWorlds : ∀ {Result} statement
    (continuation : Reply statement → X.E.Script Result) before →
    X.Interrupted (X.E.ask statement continuation) before before ×
    X.Interrupted (X.E.ask statement continuation) before (proposed statement before)
  lostAcknowledgementIncludesBothWorlds statement continuation before =
    X.beforeReply [] statement continuation before Database.acknowledgementLost before
      (X.E.stopped _) (X.unchanged before) Database.unknownBefore ,
    X.beforeReply [] statement continuation before Database.acknowledgementLost (proposed statement before)
      (X.E.stopped _) (X.unchanged before) Database.unknownAfter

-- There is no Goal, Completed, valid-input or readiness predicate to replace.
-- Inputs are the operation's admitted inputs; every one owes a lawful complete
-- execution from every represented starting world, as well as retry safety.
record Recoverable (World Input : Set) : Set₁ where
  field
    Effect : Set
    Reply : Effect → Set
  module E = Effects.Protocol Effect Reply
  field
    script : Input → E.Script Wire.Value
    Atomic : World → (effect : Effect) → Reply effect → World → Set
    intent : Over.Intent World Input
  module X = Execution World Effect Reply Atomic
  module G = Over World
  field
    converges : ∀ input initial interrupted final reply →
      X.Interrupted (script input) initial interrupted →
      X.Completed (script input) interrupted final reply →
      G.Goal intent (G.invocation input initial) final reply
    progress : ∀ input initial →
      Σ World (λ final → Σ Wire.Value (λ reply →
        X.Completed (script input) initial final reply))

  -- Ordinary completion is also checked: interrupting before the first effect
  -- leaves the initial world intact, so convergence applies to that execution.
  completedMeetsIntent : ∀ input initial final reply →
    X.Completed (script input) initial final reply →
    G.Goal intent (G.invocation input initial) final reply
  completedMeetsIntent input initial final reply execution =
    converges input initial initial final reply
      (X.atPrefix [] (script input) initial (E.stopped _) (X.unchanged initial))
      execution

  progressReachesIntent : ∀ input initial →
    Σ World (λ final → Σ Wire.Value (λ reply →
      X.Completed (script input) initial final reply ×
      G.Goal intent (G.invocation input initial) final reply))
  progressReachesIntent input initial with progress input initial
  ... | final , reply , execution =
    final , reply , execution , completedMeetsIntent input initial final reply execution
