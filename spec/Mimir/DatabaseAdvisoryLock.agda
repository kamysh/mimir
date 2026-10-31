{-# OPTIONS --safe #-}
-- Standard dependency boundary for transaction-scoped exclusive advisory
-- locks. No instance is assumed here. Mimir must establish that every
-- protected operation actually owns the same database/key lock while acting.
module Mimir.DatabaseAdvisoryLock where

open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

record Contract : Set₁ where
  field
    Snapshot Database Key Transaction : Set
    -- Transaction denotes a top-level transaction, not a savepoint.
    Held : Snapshot → Database → Key → Transaction → Set
    Ended : Snapshot → Transaction → Set
    exclusive : ∀ snapshot database key first second →
      Held snapshot database key first → Held snapshot database key second → first ≡ second
    endedReleased : ∀ snapshot database key transaction →
      Ended snapshot transaction → Held snapshot database key transaction → ⊥

module Application (locks : Contract) where
  open Contract locks

  -- The application premise is deliberately explicit: locks do not protect
  -- a writer that omits them, reads beforehand, or chooses a different key.
  noCompetingProtectedWrite : ∀ snapshot database key owner writer →
    Held snapshot database key owner → owner ≢ writer →
    Held snapshot database key writer → ⊥
  noCompetingProtectedWrite snapshot database key owner writer owned different writing = different
    (exclusive snapshot database key owner writer owned writing)
