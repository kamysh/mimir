{-# OPTIONS --safe #-}
-- A pure result transformation neither adds nor removes protocol events.
module Mimir.EffectMap where

open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.Effects as Effects

module Protocol (Effect : Set) (Reply : Effect → Set) where
  open Effects.Protocol Effect Reply

  map : ∀ {A B} → (A → B) → Script A → Script B
  map change program = program >>= λ value → done (change value)

  forward : ∀ {A B} (change : A → B) {program events value} →
    Runs program events value → Runs (map change program) events (change value)
  forward change (returned result) = returned (change result)
  forward change (replied effect continuation reply execution) =
    replied effect (λ response → map change (continuation response)) reply (forward change execution)

  backward : ∀ {A B} (change : A → B) (program : Script A) {events output} →
    Runs (map change program) events output →
    Σ A (λ value → Runs program events value × change value ≡ output)
  backward change (done value) (returned _) = value , returned value , refl
  backward change (ask effect continuation) (replied _ _ reply execution)
    with backward change (continuation reply) execution
  ... | value , original , exact = value , replied effect continuation reply original , exact
