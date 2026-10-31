{-# OPTIONS --safe #-}
module Mimir.EffectDecomposition where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
import Mimir.Effects as Effects

module Decompose (Effect : Set) (Reply : Effect → Set) where
  module E = Effects.Protocol Effect Reply
  open E

  Split : ∀ {A B} → Script A → (A → Script B) → List Event → B → Set
  Split {A} program next events result =
    Σ A λ value → Σ (List Event) λ before → Σ (List Event) λ after →
      Runs program before value × Runs (next value) after result × events ≡ before ++ after

  splitRun : ∀ {A B} (program : Script A) (next : A → Script B) {events result} →
    Runs (program >>= next) events result → Split program next events result
  splitRun (done value) next {events} run = value , [] , events , returned value , run , refl
  splitRun (ask effect continuation) next (replied _ _ reply rest)
    with splitRun (continuation reply) next rest
  ... | value , before , after , firstRun , secondRun , exact =
    value , (effect , reply) ∷ before , after , replied effect continuation reply firstRun ,
      secondRun , cong ((effect , reply) ∷_) exact
