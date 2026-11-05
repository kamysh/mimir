{-# OPTIONS --safe #-}
-- Storage caps apply to retained diagnostics, never complete task state.
module Mimir.OptionalLimit where
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤_; _≤?_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes)
Within : Maybe ℕ → ℕ → Set
Within nothing size = ⊤
Within (just maximum) size = size ≤ maximum
check : ∀ limit size → Dec (Within limit size)
check nothing size = yes tt
check (just maximum) size = size ≤? maximum
