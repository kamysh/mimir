{-# OPTIONS --safe #-}
-- Select the lexicographically least ready item, conserving every remaining
-- item. A failed selection proves that none of the supplied items is ready.
module Mimir.ReadySelection where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
import Mimir.ByteKeyOrder as Key

module Select (Item : Set) (key : Item → Key.Key)
  (Ready : Item → Set) (ready? : ∀ item → Dec (Ready item)) where

  Bound : Item → Item → Set
  Bound selected candidate = Ready candidate → ¬ (key candidate Key.< key selected)

  record Choice (input : List Item) : Set where
    constructor choice
    field
      selected : Item
      remainder : List Item
      partition : input Perm.↭ (selected ∷ remainder)
      ready : Ready selected
      least : All (Bound selected) input

  data Outcome (input : List Item) : Set where
    none : All (λ item → ¬ Ready item) input → Outcome input
    chosen : Choice input → Outcome input

  blockedBound : ∀ selected input → All (λ item → ¬ Ready item) input → All (Bound selected) input
  blockedBound selected [] [] = []
  blockedBound selected (item ∷ rest) (blocked ∷ tail) =
    (λ ready → ⊥-elim (blocked ready)) ∷ blockedBound selected rest tail

  lowerBound : ∀ first second input → key first Key.< key second →
    All (Bound second) input → All (Bound first) input
  lowerBound first second [] before [] = []
  lowerBound first second (item ∷ rest) before (bound ∷ tail) =
    (λ ready earlier → bound ready (Key.trans earlier before)) ∷ lowerBound first second rest before tail

  equalBound : ∀ first second input → key first ≡ key second →
    All (Bound second) input → All (Bound first) input
  equalBound first second input same bounds =
    subst (λ limit → All (λ candidate → Ready candidate → ¬ (key candidate Key.< limit)) input)
      (sym same) bounds

  liftPartition : ∀ (item selected : Item) (rest remainder : List Item) → rest Perm.↭ (selected ∷ remainder) →
    (item ∷ rest) Perm.↭ (selected ∷ item ∷ remainder)
  liftPartition item selected rest remainder partition =
    Perm.trans (Perm.prep item partition) (Perm.swap item selected Perm.refl)

  select : ∀ input → Outcome input
  select [] = none []
  select (item ∷ rest) with ready? item | select rest
  ... | no blocked | none unavailable = none (blocked ∷ unavailable)
  ... | yes ready | none unavailable = chosen
    (choice item rest Perm.refl ready
      ((λ _ → Key.irreflexive (key item)) ∷ blockedBound item rest unavailable))
  ... | no blocked | chosen (choice selected remainder partition ready least) = chosen
    (choice selected (item ∷ remainder) (liftPartition item selected rest remainder partition) ready
      ((λ ready → ⊥-elim (blocked ready)) ∷ least))
  ... | yes headReady | chosen (choice selected remainder partition ready least)
    with Key.compare (key item) (key selected)
  ...   | tri< before different notAfter = chosen
    (choice item rest Perm.refl headReady
      ((λ _ → Key.irreflexive (key item)) ∷ lowerBound item selected rest before least))
  ...   | tri≈ notBefore same notAfter = chosen
    (choice item rest Perm.refl headReady
      ((λ _ → Key.irreflexive (key item)) ∷ equalBound item selected rest same least))
  ...   | tri> notBefore different after = chosen
    (choice selected (item ∷ remainder) (liftPartition item selected rest remainder partition) ready
      ((λ _ → notBefore) ∷ least))
