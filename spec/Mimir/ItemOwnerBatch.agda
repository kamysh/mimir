{-# OPTIONS --safe #-}
-- Both recording and review extraction reserve item provenance through this
-- batch. A later conflict returns no partial registry for publication. Stable
-- identity, source and actor survive correction and removal from active views.
module Mimir.ItemOwnerBatch where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; cong)
open import Mimir.LearningSchema using (LearningItem)
open import Mimir.Validation using (Fault)
import Mimir.ItemOwners as Owners

owner : ℕ → LearningItem → Owners.Owner
owner experience item = experience , LearningItem.reference item , LearningItem.actor item

data Batch (experience : ℕ) : Owners.Registry → List LearningItem → Owners.Registry → Set where
  done : ∀ before → Batch experience before [] before
  next : ∀ {before item rest middle after} →
    Owners.reserve before (LearningItem.identity item) (owner experience item) ≡ Owners.reserved middle →
    Batch experience middle rest after → Batch experience before (item ∷ rest) after

Prepared : ℕ → Owners.Registry → List LearningItem → Set
Prepared experience before items = Σ Owners.Registry (Batch experience before items)

prepare : ∀ experience before items → Fault ⊎ Prepared experience before items
prepare experience before [] = inj₂ (before , done before)
prepare experience before (item ∷ rest)
  with Owners.reserve before (LearningItem.identity item) (owner experience item) in accepted
... | Owners.refused failure = inj₁ failure
... | Owners.reserved middle with prepare experience middle rest
...   | inj₁ failure = inj₁ failure
...   | inj₂ (after , remaining) = inj₂ (after , next accepted remaining)

acceptedPreserves : ∀ before identity proposedOwner after →
  Owners.reserve before identity proposedOwner ≡ Owners.reserved after → ∀ key old →
  before key ≡ just old → after key ≡ just old
acceptedPreserves before identity proposedOwner after accepted key old original with key ≟ identity
... | yes refl = trans (sym (cong (λ outcome → Owners.after before outcome identity) accepted)) (Owners.existingOwnershipImmutable before identity old proposedOwner original)
... | no different = trans (sym (cong (λ outcome → Owners.after before outcome key) accepted)) (trans (Owners.noOtherItemChanges before identity key proposedOwner different) original)

batchPreserves : ∀ {experience before items after} → Batch experience before items after →
  ∀ key old → before key ≡ just old → after key ≡ just old
batchPreserves (done before) key old original = original
batchPreserves {experience} {before} (next {item = item} accepted remaining) key old original = batchPreserves remaining key old
  (acceptedPreserves before (LearningItem.identity item)
   (owner experience item) _ accepted key old original)

Owns : ℕ → Owners.Registry → LearningItem → Set
Owns experience registry item = registry (LearningItem.identity item) ≡ just (owner experience item)

allOwned : ∀ {experience before items after} → Batch experience before items after →
  All (Owns experience after) items
allOwned (done before) = []
allOwned {experience} {before} (next {item = item} accepted remaining) = batchPreserves remaining _ _
  (Owners.acceptedOwnsItem before (LearningItem.identity item)
   (owner experience item) _ accepted)
  ∷ allOwned remaining

unmentionedUnchanged : ∀ {experience before items after} → Batch experience before items after →
  ∀ key → All (λ item → key ≢ LearningItem.identity item) items → after key ≡ before key
unmentionedUnchanged (done before) key [] = refl
unmentionedUnchanged {experience} {before} (next {item = item} accepted remaining) key (different ∷ differences) = trans (unmentionedUnchanged remaining key differences)
  (trans
   (sym (cong (λ outcome → Owners.after before outcome key) accepted))
   (Owners.noOtherItemChanges before (LearningItem.identity item) key
    (owner experience item) different))
