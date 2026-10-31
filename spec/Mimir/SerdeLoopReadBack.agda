{-# OPTIONS --safe #-}
-- Successful loop transitions compose without exposing the fuel implementation.
import Mimir.FloatConversion
module Mimir.SerdeLoopReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl; subst; sym)
import Mimir.SerdeFlow as Flow
import Mimir.SerdeLoop as Loop
import Mimir.SerdeReadBack as Back
import Mimir.SerdeReadBackComposition as ComposeDependency
private
  module Compose = ComposeDependency floatConversion

module Machine (State Value : Set)
  (transition : State → ∀ input → Loop.Step State Value input) where
  private module Run = Loop.Machine State Value transition

  finish : ∀ state input value suffix →
    Back.Returned (Loop.Step.result (transition state input)) (inj₂ value) suffix →
    Back.Returned (Run.read state input) value suffix
  finish state input value suffix receipt = Back.returned (Back.Returned.position receipt)
    (Run.complete state input _
     (Run.completed value (Back.Returned.position receipt)
      (Back.Returned.observed receipt)))
    (Back.Returned.remaining receipt)

  next : ∀ state input following middle value suffix →
    Back.Returned (Loop.Step.result (transition state input)) (inj₁ following) middle →
    Back.Returned (Run.read following middle) value suffix →
    Back.Returned (Run.read state input) value suffix
  next state input following .(Flow.F.Cursor.remaining position) value suffix
    (Back.returned position observed refl) tail = subst (λ result → Back.Returned result value suffix)
      (sym
       (Run.complete state input _
        (Run.continued following position observed
         (Run.read following (Flow.F.Cursor.remaining position))
         (Run.faithful following (Flow.F.Cursor.remaining position)))))
      (Compose.prefix position tail)
