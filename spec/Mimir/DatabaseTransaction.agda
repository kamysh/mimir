{-# OPTIONS --safe #-}
-- A dependency contract, not an implementation of PostgreSQL. State denotes
-- the transaction publication view at its commit boundary, not an assertion
-- that concurrent transactions cannot subsequently change the database.
module Mimir.DatabaseTransaction where

data Receipt : Set where
  committed aborted acknowledgementLost : Receipt

data Atomic {State : Set} (before proposed : State) : Receipt → State → Set where
  committedAll : Atomic before proposed committed proposed
  abortedNone : Atomic before proposed aborted before
  unknownBefore : Atomic before proposed acknowledgementLost before
  unknownAfter : Atomic before proposed acknowledgementLost proposed

-- Completed observations only: this interface neither guarantees that an
-- operation terminates nor supplies Mimir's statements, locks, or write set.
-- A concrete adapter must relate its completed calls to these observations.
record Contract (State : Set) : Set₁ where
  field
    Completion : Set
    before proposed published : Completion → State
    receipt : Completion → Receipt
    atomicity : ∀ event → Atomic (before event) (proposed event) (receipt event) (published event)

-- Application invariants must hold on BOTH possible publications before a
-- lost acknowledgement can be handled safely. No rollback is inferred.
invariantPreserved : ∀ {State : Set} (Invariant : State → Set)
  {before proposed observed actual} → Atomic before proposed observed actual →
  Invariant before → Invariant proposed → Invariant actual
invariantPreserved Invariant committedAll old new = new
invariantPreserved Invariant abortedNone old new = old
invariantPreserved Invariant unknownBefore old new = old
invariantPreserved Invariant unknownAfter old new = new
