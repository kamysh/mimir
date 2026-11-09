{-# OPTIONS --safe #-}
-- The first physical defeat, not the correcting belief's creation date,
-- starts the user's waiting period. Legacy expiry is an explicit migration
-- result; an absent new clock is never interpreted as legacy expiry.
module Mimir.RetirementClock where

open import Data.Bool using (Bool; true)
open import Data.Integer using (ℤ; _-_; _≤?_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Clock : Set where
  firstDefeat : ℤ → Clock
  legacyExpired : Clock

recordFirst : ℤ → Maybe Clock → Clock
recordFirst now nothing = firstDefeat now
recordFirst now (just original) = original

waitingSatisfied : ℤ → ℤ → Clock → Bool
waitingSatisfied now grace (firstDefeat first) = does (grace ≤? (now - first))
waitingSatisfied now grace legacyExpired = true

-- A second defeat or a restarted statement cannot extend the waiting time.
laterDefeatKeepsFirst : ∀ first later original →
  recordFirst later (just (recordFirst first original)) ≡ recordFirst first original
laterDefeatKeepsFirst first later nothing = refl
laterDefeatKeepsFirst first later (just original) = refl

legacyWaitIsOver : ∀ now grace → waitingSatisfied now grace legacyExpired ≡ true
legacyWaitIsOver now grace = refl

laterDefeatCannotReviveLegacyGrace : ∀ later → recordFirst later (just legacyExpired) ≡ legacyExpired
laterDefeatCannotReviveLegacyGrace later = refl
