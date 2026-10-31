{-# OPTIONS --safe #-}
-- Interrupted implementations expose only completed high-level receipts.
-- The current low-level handler and its exact residual program are retained.
module Mimir.EffectsHandlingPrefix where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
import Mimir.Effects as Effects
import Mimir.EffectsHandling as Handling
import Mimir.EffectsPrefixComposition as Composition

module With (High : Set) (HighReply : High → Set)
  (Low : Set) (LowReply : Low → Set)
  (handler : (operation : High) → Effects.Protocol.Script Low LowReply (HighReply operation)) where
  module H = Effects.Protocol High HighReply
  module L = Effects.Protocol Low LowReply
  module Lower = Handling.With High HighReply Low LowReply handler
  module Bind = Composition.With Low LowReply

  data Partial {A : Set} : H.Script A → List L.Event → L.Script A → Set where
    boundary : ∀ program → Partial program [] (Lower.lower program)
    pending : ∀ operation continue current {events residual} →
      L.Prefix (handler operation) events current →
      residual ≡ (current L.>>= (λ reply → Lower.lower (continue reply))) →
      Partial (H.ask operation continue) events residual
    progressed : ∀ operation continue reply {before after residual} →
      L.Runs (handler operation) before reply → Partial (continue reply) after residual →
      Partial (H.ask operation continue) (before ++ after) residual

  reflect : ∀ {A : Set} (program : H.Script A) {events residual} →
    L.Prefix (Lower.lower program) events residual → Partial program events residual
  reflect (H.done value) (L.Prefix.stopped _) = boundary _
  reflect (H.ask operation continue) {events} {residual} receipt
    with Bind.split (handler operation) (λ reply → Lower.lower (continue reply)) receipt
  ... | Bind.within current earlier exact = pending operation continue current earlier exact
  ... | Bind.beyond reply before after finished later exact = subst (λ trace → Partial (H.ask operation continue) trace residual)
    (sym exact)
    (progressed operation continue reply finished
     (reflect (continue reply) later))

  completedEvents : ∀ {A} {program : H.Script A} {events residual} →
    Partial program events residual → List H.Event
  completedEvents (boundary program) = []
  completedEvents (pending operation continue current earlier exact) = []
  completedEvents (progressed operation continue reply finished later) =
    (operation , reply) ∷ completedEvents later

  highResidual : ∀ {A} {program : H.Script A} {events residual} →
    Partial program events residual → H.Script A
  highResidual (boundary program) = program
  highResidual (pending operation continue current earlier exact) = H.ask operation continue
  highResidual (progressed operation continue reply finished later) = highResidual later

  project : ∀ {A} {program : H.Script A} {events residual} (receipt : Partial program events residual) →
    H.Prefix program (completedEvents receipt) (highResidual receipt)
  project (boundary program) = H.Prefix.stopped _
  project (pending operation continue current earlier exact) = H.Prefix.stopped _
  project (progressed operation continue reply finished later) = H.Prefix.replied operation continue reply (project later)

  realize : ∀ {A} {program : H.Script A} {events residual} →
    Partial program events residual → L.Prefix (Lower.lower program) events residual
  realize (boundary program) = L.Prefix.stopped _
  realize (pending operation continue current earlier exact) = subst
    (λ residual →
       L.Prefix (Lower.lower (H.ask operation continue)) _ residual)
    (sym exact)
    (Bind.bindWithin (λ reply → Lower.lower (continue reply)) earlier)
  realize (progressed operation continue reply finished later) = Bind.bindAfter finished (realize later)
