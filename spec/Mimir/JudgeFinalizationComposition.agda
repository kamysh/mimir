{-# OPTIONS --safe #-}
-- Finalization relates incident and status outcomes to the judge workflow.
-- Notification delivery is an external operation.
module Mimir.JudgeFinalizationComposition where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₂)
open import Data.Unit using (⊤)
open import Mimir.Text using (Text)
import Mimir.JudgeFinalization as Finalization
import Mimir.JudgeStateOperations as State
open import Relation.Binary.PropositionalEquality using (_≡_)

module Bound where

  Receipt : (effect : Finalization.Effect) → Finalization.Reply effect → Set
  Receipt Finalization.clock reply = ⊤
  Receipt (Finalization.finishTrace id report) reply = ⊤
  Receipt (Finalization.reportProblem whereFailed detail) reply = ⊤
  Receipt (Finalization.recordIncident report confirmation) reply = State.IncidentExecution report confirmation reply
  Receipt (Finalization.writeStatus report) reply = ⊤
  Receipt (Finalization.notify report) reply = ⊤

  data Runs {A : Set} : Finalization.E.Script A → List Finalization.E.Event → A → Set where
    returned : ∀ value → Runs (Finalization.E.done value) [] value
    replied : ∀ effect continuation reply events value → Receipt effect reply →
      Runs (continuation reply) events value →
      Runs (Finalization.E.ask effect continuation) ((effect , reply) ∷ events) value
