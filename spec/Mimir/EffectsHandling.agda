{-# OPTIONS --safe #-}
-- Replace abstract requests by concrete protocols and reconstruct every
-- high-level receipt from an actual completed handler execution. The theorem
-- does not assume that arbitrary handlers satisfy a particular domain law;
-- those are proved for the selected handlers at their composition sites.
module Mimir.EffectsHandling where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
import Mimir.Effects as E
import Mimir.EffectsComposition as C

module With (High : Set) (HighReply : High → Set)
  (Low : Set) (LowReply : Low → Set)
  (handler : (operation : High) → E.Protocol.Script Low LowReply (HighReply operation)) where
  module H = E.Protocol High HighReply
  module L = E.Protocol Low LowReply
  module Composition = C.With Low LowReply

  lower : ∀ {A : Set} → H.Script A → L.Script A
  lower (H.done value) = L.done value
  lower (H.ask operation continue) = handler operation L.>>= (λ reply → lower (continue reply))

  data Handled : List H.Event → List L.Event → Set where
    empty : Handled [] []
    more : ∀ operation reply {before events after} → L.Runs (handler operation) before reply →
      Handled events after → Handled ((operation , reply) ∷ events) (before ++ after)

  record Refinement {A : Set} (program : H.Script A) (events : List L.Event) (result : A) : Set where
    constructor refinement
    field
      highEvents : List H.Event
      highRun : H.Runs program highEvents result
      handled : Handled highEvents events

  refine : ∀ {A : Set} (program : H.Script A) {events result} →
    L.Runs (lower program) events result → Refinement program events result
  refine (H.done value) (L.returned _) = refinement [] (H.returned _) empty
  refine (H.ask operation continue) run with Composition.splitBind (handler operation)
    (λ reply → lower (continue reply)) run
  ... | Composition.split reply before after handlerRun later exact with refine (continue reply) later
  ... | refinement highEvents highRun handled =
    refinement ((operation , reply) ∷ highEvents)
      (H.replied operation continue reply highRun)
      (subst (Handled ((operation , reply) ∷ highEvents)) (sym exact)
        (more operation reply handlerRun handled))
