{-# OPTIONS --safe #-}
-- Proposed standard dependency boundary: a successful ordinary read-only
-- SELECT in READ COMMITTED, without FOR UPDATE/SHARE, sees the committed row
-- state at statement start plus earlier writes in its own transaction.
-- This excludes sequences, external side effects, DML and volatile functions
-- that perform their own writes. No instance or postulate is supplied here.
-- SQL evaluation, isolation selection, handle identity, lock coverage and
-- the actual committed/prior-write projections remain adapter obligations.
module Mimir.DatabaseReadCommitted where

open import Relation.Binary.PropositionalEquality using (_≡_; cong; trans)

record Contract (State : Set) : Set₁ where
  field
    Read : Set
    committedAtStart snapshot : Read → State
    ownPriorWrites : Read → State → State
    visibility : ∀ event → snapshot event ≡ ownPriorWrites event (committedAtStart event)

module Application {State : Set} (reads : Contract State) where
  open Contract reads

  -- The caller must establish the prior publication is still the committed
  -- state and that this read precedes its own modifications. A lock request
  -- alone establishes neither premise.
  readsPriorPublication : ∀ event prior → committedAtStart event ≡ prior →
    ownPriorWrites event prior ≡ prior → snapshot event ≡ prior
  readsPriorPublication event prior current untouched =
    trans (visibility event) (trans (cong (ownPriorWrites event) current) untouched)
