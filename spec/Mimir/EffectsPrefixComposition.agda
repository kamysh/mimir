{-# OPTIONS --safe #-}
-- An interrupted bind is either inside its first computation, or follows an
-- actual first-computation receipt and is inside the continuation.
module Mimir.EffectsPrefixComposition where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
import Mimir.Effects as Effects

module With (Operation : Set) (Reply : Operation → Set) where
  open Effects.Protocol Operation Reply

  data Split {A B : Set} (first : Script A) (next : A → Script B)
    (events : List Event) (residual : Script B) : Set where
    within : ∀ current → Prefix first events current → residual ≡ (current >>= next) →
      Split first next events residual
    beyond : ∀ value before after → Runs first before value → Prefix (next value) after residual →
      events ≡ before ++ after → Split first next events residual

  split : ∀ {A B : Set} (first : Script A) (next : A → Script B) {events residual} →
    Prefix (first >>= next) events residual → Split first next events residual
  split (done value) next receipt = beyond value [] _ (Runs.returned value) receipt refl
  split first@(ask operation continue) next (Prefix.stopped _) = within (ask operation continue) (Prefix.stopped _) refl
  split (ask operation continue) next (Prefix.replied .operation _ reply {events} receipt)
    with split (continue reply) next receipt
  ... | within current earlier exact = within current (Prefix.replied operation continue reply earlier)
    exact
  ... | beyond value before after finished later exact = beyond value ((operation , reply) ∷ before) after
    (Runs.replied operation continue reply finished) later
    (cong ((operation , reply) ∷_) exact)

  bindWithin : ∀ {A B : Set} {first current : Script A} {events} (next : A → Script B) →
    Prefix first events current → Prefix (first >>= next) events (current >>= next)
  bindWithin next (Prefix.stopped first) = Prefix.stopped _
  bindWithin next (Prefix.replied operation continue reply earlier) = Prefix.replied operation (λ response → continue response >>= next)
    reply (bindWithin next earlier)

  bindAfter : ∀ {A B : Set} {first : Script A} {next : A → Script B}
    {before after value residual} → Runs first before value → Prefix (next value) after residual →
    Prefix (first >>= next) (before ++ after) residual
  bindAfter (Runs.returned value) later = later
  bindAfter (Runs.replied operation continue reply finished) later = Prefix.replied operation _ reply (bindAfter finished later)
