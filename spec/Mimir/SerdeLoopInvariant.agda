{-# OPTIONS --safe #-}
-- A transition invariant extends to every finite visitor execution, including
-- arbitrary nesting of continuing steps and cursor prefix composition.
module Mimir.SerdeLoopInvariant where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
import Mimir.SerdeLoop as Loop
import Mimir.SerdeFlow as Flow
import Mimir.SerdeSuccess as S

module Machine (State Value : Set) (transition : State → ∀ input → Loop.Step State Value input)
  (stateProperty : State → Set) (valueProperty : Value → Set) where
  module M = Loop.Machine State Value transition

  Next : State ⊎ Value → Set
  Next (inj₁ state) = stateProperty state
  Next (inj₂ value) = valueProperty value

  module Laws (stepValid : ∀ state input → stateProperty state →
    S.Ensures Next (Loop.Step.result (transition state input))) where

    execution : ∀ {state input result} → M.Execution state input result →
      stateProperty state → S.Ensures valueProperty result
    execution (M.rejected error exact) holds = tt
    execution (M.panicked position exact) holds = tt
    execution {state} {input} (M.completed value position exact) holds =
      S.extract Next (Loop.Step.result (transition state input)) (inj₂ value) position
        (stepValid state input holds) exact
    execution {state} {input} (M.continued following position exact result executed) holds =
      S.prefix valueProperty position result (execution executed
        (S.extract Next (Loop.Step.result (transition state input)) (inj₁ following) position
          (stepValid state input holds) exact))

    read : ∀ state input → stateProperty state → S.Ensures valueProperty (M.read state input)
    read state input holds = execution (M.faithful state input) holds
