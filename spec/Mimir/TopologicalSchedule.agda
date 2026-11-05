{-# OPTIONS --safe #-}
-- Total dependency scheduling with no fuel-exhaustion result: the bound is
-- proved from removal of exactly one pending item. Every emitted item was
-- ready and lexicographically least; a blocked suffix admits no next step.
module Mimir.TopologicalSchedule where

open import Data.List using (List; []; _∷_; _++_; length)
import Data.List.Properties as List
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as Perm
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; s≤s⁻¹; _≟_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; trans; cong)
import Mimir.ByteKeyOrder as Key
import Mimir.ReadySelection as Selection
open import Mimir.Collections using (all?; module Equality)

module Schedule (Item : Set) (key : Item → Key.Key) (requires : Item → List Key.Key) where
  module Names = Equality Key.Key (List.≡-dec _≟_)

  Ready : List Key.Key → Item → Set
  Ready completed item = All (λ dependency → Names.Present dependency completed) (requires item)

  ready? : ∀ completed item → Dec (Ready completed item)
  ready? completed item = all? (λ dependency → Names.present? dependency completed) (requires item)

  module Select (completed : List Key.Key) = Selection.Select Item key (Ready completed) (ready? completed)

  data Nonempty : List Item → Set where cons : ∀ item rest → Nonempty (item ∷ rest)

  data Plan (completed : List Key.Key) : List Item → Set where
    finished : Plan completed []
    blocked : ∀ {pending} → Nonempty pending → All (λ item → ¬ Ready completed item) pending →
      Plan completed pending
    emit : ∀ {pending} (selection : Select.Choice completed pending) →
      Plan (key (Select.Choice.selected selection) ∷ completed) (Select.Choice.remainder selection) →
      Plan completed pending

  smaller : ∀ fuel (pending : List Item) (selected : Item) remainder → pending Perm.↭ (selected ∷ remainder) →
    length pending ≤ suc fuel → length remainder ≤ fuel
  smaller fuel pending selected remainder partition bounded =
    s≤s⁻¹ (subst (_≤ suc fuel) (Perm.↭-length partition) bounded)

  plan : ∀ fuel completed pending → length pending ≤ fuel → Plan completed pending
  plan fuel completed [] bounded = finished
  plan zero completed (item ∷ rest) ()
  plan (suc fuel) completed pending@(item ∷ rest) bounded with Select.select completed pending
  ... | Select.none unavailable = blocked (cons item rest) unavailable
  ... | Select.chosen selection = emit selection
    (plan fuel (key (Select.Choice.selected selection) ∷ completed) (Select.Choice.remainder selection)
      (smaller fuel pending (Select.Choice.selected selection) (Select.Choice.remainder selection)
        (Select.Choice.partition selection) bounded))

  schedule : ∀ completed pending → Plan completed pending
  schedule completed pending = plan (length pending) completed pending ≤-refl

  emitted : ∀ {completed pending} → Plan completed pending → List Item
  emitted finished = []
  emitted (blocked nonempty unavailable) = []
  emitted (emit selection rest) = Select.Choice.selected selection ∷ emitted rest

  remaining : ∀ {completed pending} → Plan completed pending → List Item
  remaining finished = []
  remaining {pending = pending} (blocked nonempty unavailable) = pending
  remaining (emit selection rest) = remaining rest

  Ordered : List Key.Key → List Item → Set
  Ordered completed [] = ⊤
  Ordered completed (item ∷ rest) = Ready completed item × Ordered (key item ∷ completed) rest

  allDependenciesPrecede : ∀ {completed pending} (execution : Plan completed pending) →
    Ordered completed (emitted execution)
  allDependenciesPrecede finished = tt
  allDependenciesPrecede (blocked nonempty unavailable) = tt
  allDependenciesPrecede (emit selection rest) = Select.Choice.ready selection , allDependenciesPrecede rest

  conservation : ∀ {completed pending} (execution : Plan completed pending) →
    pending Perm.↭ (emitted execution ++ remaining execution)
  conservation finished = Perm.refl
  conservation (blocked nonempty unavailable) = Perm.refl
  conservation (emit selection rest) = Perm.trans (Select.Choice.partition selection)
    (Perm.prep (Select.Choice.selected selection) (conservation rest))

  completedAfter : List Key.Key → List Item → List Key.Key
  completedAfter completed [] = completed
  completedAfter completed (item ∷ rest) = completedAfter (key item ∷ completed) rest

  terminalHasNoReadyItem : ∀ {completed pending} (execution : Plan completed pending) →
    All (λ item → ¬ Ready (completedAfter completed (emitted execution)) item) (remaining execution)
  terminalHasNoReadyItem finished = []
  terminalHasNoReadyItem (blocked nonempty unavailable) = unavailable
  terminalHasNoReadyItem (emit selection rest) = terminalHasNoReadyItem rest

  nonemptyCannotPermuteToEmpty : ∀ pending → Nonempty pending → pending Perm.↭ [] → ⊥
  nonemptyCannotPermuteToEmpty (item ∷ rest) (cons _ _) permutation with Perm.↭-length permutation
  ... | ()

  blockedHasNoOrdering : ∀ completed pending → Nonempty pending →
    All (λ item → ¬ Ready completed item) pending →
    ∀ ordering → pending Perm.↭ ordering → Ordered completed ordering → ⊥
  blockedHasNoOrdering completed pending nonempty unavailable [] permutation ordered =
    nonemptyCannotPermuteToEmpty pending nonempty permutation
  blockedHasNoOrdering completed pending nonempty unavailable (item ∷ rest) permutation (ready , ordered)
    with Perm.All-resp-↭ permutation unavailable
  ... | notReady ∷ remaining = notReady ready

  completedConservesAll : ∀ {completed pending} (execution : Plan completed pending) →
    remaining execution ≡ [] → pending Perm.↭ emitted execution
  completedConservesAll {pending = pending} execution empty =
    subst (pending Perm.↭_)
      (trans (cong (emitted execution ++_) empty) (List.++-identityʳ (emitted execution)))
      (conservation execution)
