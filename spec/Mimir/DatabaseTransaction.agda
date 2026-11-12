{-# OPTIONS --safe #-}
-- The client receives the result of every committed transaction. State is
-- the publication view at the commit boundary.
module Mimir.DatabaseTransaction where

data Receipt : Set where
  committed aborted : Receipt

data Atomic {State : Set} (before proposed : State) : Receipt → State → Set where
  committedAll : Atomic before proposed committed proposed
  abortedNone : Atomic before proposed aborted before

-- Completed observations only: this interface neither guarantees that an
-- operation terminates nor supplies Mimir's statements, locks, or write set.
-- A concrete adapter must relate its completed calls to these observations.
record Contract (State : Set) : Set₁ where
  field
    Completion : Set
    before proposed published : Completion → State
    receipt : Completion → Receipt
    atomicity : ∀ event → Atomic (before event) (proposed event) (receipt event) (published event)

-- Application invariants hold for both a commit and an unsuccessful attempt.
invariantPreserved : ∀ {State : Set} (Invariant : State → Set)
  {before proposed observed actual} → Atomic before proposed observed actual →
  Invariant before → Invariant proposed → Invariant actual
invariantPreserved Invariant committedAll old new = new
invariantPreserved Invariant abortedNone old new = old
