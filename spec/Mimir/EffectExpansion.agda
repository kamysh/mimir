{-# OPTIONS --safe #-}
-- Substituting a protocol implementation for each abstract operation. The
-- relation retains both the abstract receipt and the complete concrete trace;
-- no implementation/refinement claim is obtained merely by naming an effect.
module Mimir.EffectExpansion where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (refl)
import Mimir.Effects as Effects
import Mimir.EffectDecomposition as Decomposition

module Expand (Source : Set) (SourceReply : Source → Set)
  (Target : Set) (TargetReply : Target → Set) where
  module S = Effects.Protocol Source SourceReply
  module T = Effects.Protocol Target TargetReply
  module D = Decomposition.Decompose Target TargetReply

  module With (implementation : (operation : Source) → T.Script (SourceReply operation)) where
    expand : ∀ {A} → S.Script A → T.Script A
    expand (S.done result) = T.done result
    expand (S.ask operation continuation) =
      implementation operation T.>>= (λ reply → expand (continuation reply))

    data Translation : List S.Event → List T.Event → Set where
      empty : Translation [] []
      operation : ∀ effect reply {events sourceRest targetRest} →
        T.Runs (implementation effect) events reply →
        Translation sourceRest targetRest →
        Translation ((effect , reply) ∷ sourceRest) (events ++ targetRest)

    translateRun : ∀ {A} {program : S.Script A} {sourceEvents targetEvents result} →
      S.Runs program sourceEvents result → Translation sourceEvents targetEvents →
      T.Runs (expand program) targetEvents result
    translateRun (S.returned result) empty = T.returned result
    translateRun (S.replied _ _ _ rest) (operation _ _ run translation) =
      T.bindRuns run (translateRun rest translation)

    -- Conversely, every completed concrete run decomposes into actual
    -- implementations of the source operations. No extra concrete effects
    -- may be discarded and no abstract receipt may be invented.
    reflectRun : ∀ {A} (program : S.Script A) {targetEvents result} →
      T.Runs (expand program) targetEvents result →
      Σ (List S.Event) λ sourceEvents →
        S.Runs program sourceEvents result × Translation sourceEvents targetEvents
    reflectRun (S.done result) (T.returned _) = [] , S.returned result , empty
    reflectRun (S.ask effect continuation) run
      with D.splitRun (implementation effect) (λ reply → expand (continuation reply)) run
    ... | reply , before , after , firstRun , secondRun , refl
      with reflectRun (continuation reply) secondRun
    ... | sourceEvents , sourceRun , translation =
      (effect , reply) ∷ sourceEvents , S.replied effect continuation reply sourceRun ,
        operation effect reply firstRun translation
