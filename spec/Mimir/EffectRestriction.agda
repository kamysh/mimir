{-# OPTIONS --safe #-}
-- Closed effect sets compose through bind and apply to finite prefixes as
-- well as completed executions. No claim is made about an unreturned reply.
module Mimir.EffectRestriction where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (proj₁)
import Mimir.Effects as Effects

module Restricted (Effect : Set) (Reply : Effect → Set) (Allowed : Effect → Set) where
  module E = Effects.Protocol Effect Reply
  open E

  data Uses {A : Set} : Script A → Set where
    returned : ∀ value → Uses (done value)
    requested : ∀ effect continuation → Allowed effect →
      (∀ reply → Uses (continuation reply)) → Uses (ask effect continuation)

  bindUses : ∀ {A B} {program : Script A} {next : A → Script B} →
    Uses program → (∀ value → Uses (next value)) → Uses (program >>= next)
  bindUses (returned value) next = next value
  bindUses (requested effect continuation allowed rest) next =
    requested effect _ allowed (λ reply → bindUses (rest reply) next)

  runUses : ∀ {A} {program : Script A} {events result} →
    Uses program → Runs program events result → All (λ event → Allowed (proj₁ event)) events
  runUses (returned _) (returned _) = []
  runUses (requested _ _ allowed rest) (replied _ _ reply run) =
    allowed ∷ runUses (rest reply) run

  prefixUses : ∀ {A} {program residual : Script A} {events} →
    Uses program → Prefix program events residual → All (λ event → Allowed (proj₁ event)) events
  prefixUses permitted (stopped _) = []
  prefixUses (requested _ _ allowed rest) (replied _ _ reply prefix) =
    allowed ∷ prefixUses (rest reply) prefix
