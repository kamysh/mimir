{-# OPTIONS --safe #-}
-- Decomposition of an executed sequential protocol into its actual two
-- executions. Used to connect nested filesystem routines to receipt laws.
module Mimir.EffectsComposition where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
import Mimir.Effects as E

module With (Operation : Set) (Reply : Operation → Set) where
  open E.Protocol Operation Reply

  record Split {A B : Set} (first : Script A) (next : A → Script B)
    (events : List Event) (result : B) : Set where
    constructor split
    field
      middle : A
      before after : List Event
      firstRun : Runs first before middle
      nextRun : Runs (next middle) after result
      exact : events ≡ before ++ after

  splitBind : ∀ {A B} (first : Script A) (next : A → Script B)
    {events result} → Runs (first >>= next) events result → Split first next events result
  splitBind (done value) next run = split value [] _ (returned value) run refl
  splitBind (ask operation continue) next (replied _ _ reply run)
    with splitBind (continue reply) next run
  ... | split middle before after firstRun nextRun exact =
    split middle ((operation , reply) ∷ before) after
      (replied operation continue reply firstRun) nextRun
      (cong ((operation , reply) ∷_) exact)

  mapResult : ∀ {A B : Set} → (A → B) → Script A → Script B
  mapResult function program = program >>= (λ value → done (function value))

  unmap : ∀ {A B : Set} (function : A → B) (program : Script A)
    {events result} → Runs (mapResult function program) events result →
    Σ A (λ value → Runs program events value × function value ≡ result)
  unmap function (done value) (returned _) = value , returned value , refl
  unmap function (ask operation continue) (replied _ _ reply rest)
    with unmap function (continue reply) rest
  ... | value , run , exact = value , replied operation continue reply run , exact
