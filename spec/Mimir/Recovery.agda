{-# OPTIONS --safe #-}
-- The recovery goal is fixed here, outside operation implementations. Neither
-- an alternative predicate nor an operation-chosen observation is a field.
module Mimir.Recovery where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
import Mimir.ApplicationStore as Store
import Mimir.StructuredValue as Wire

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
