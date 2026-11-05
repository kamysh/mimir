{-# OPTIONS --safe #-}
-- Execute an effect script with a concrete, proof-indexed responder. Every
-- returned event carries equality with that responder's actual answer.
module Mimir.EffectsInterpret where

open import Data.List using (List; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.Effects as Effects

module With (Effect : Set) (Reply : Effect → Set) (Admitted : Effect → Set)
  (respond : ∀ effect → Admitted effect → Reply effect) where
  module P = Effects.Protocol Effect Reply

  data Supported {A : Set} : P.Script A → Set where
    returned : ∀ value → Supported (P.done value)
    requested : ∀ effect next → Admitted effect → (∀ reply → Supported (next reply)) → Supported (P.ask effect next)

  Receipt : P.Event → Set
  Receipt (effect , reply) = Σ (Admitted effect) (λ valid → reply ≡ respond effect valid)

  record Evaluation {A : Set} (program : P.Script A) : Set where
    constructor evaluation
    field
      result : A
      events : List P.Event
      run : P.Runs program events result
      receipts : All.All Receipt events

  prepend : ∀ {A : Set} effect (next : Reply effect → P.Script A) valid →
    Evaluation (next (respond effect valid)) → Evaluation (P.ask effect next)
  prepend effect next valid (evaluation result events run receipts) =
    evaluation result ((effect , respond effect valid) ∷ events)
      (P.replied effect next (respond effect valid) run) ((valid , refl) All.∷ receipts)

  evaluate : ∀ {A : Set} (program : P.Script A) → Supported program → Evaluation program
  evaluate (P.done value) (returned .value) = evaluation value [] (P.returned value) All.[]
  evaluate (P.ask effect next) (requested .effect .next valid supported) =
    prepend effect next valid (evaluate (next (respond effect valid)) (supported (respond effect valid)))
