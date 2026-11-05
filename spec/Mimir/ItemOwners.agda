{-# OPTIONS --safe #-}
-- The ownership ledger reserves item provenance independently of mutable
-- predictions/conditions and of whether an item remains in the active review.
module Mimir.ItemOwners where

import Data.Empty

open import Data.List using ([])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.Collections using (pairEqual)
open import Mimir.Validation using (Fault; fault; wrongIdentity)
import Mimir.LearningContracts as Contracts

Owner = ℕ × (Text × Text)
Registry = ℕ → Maybe Owner

ownerEqual = pairEqual _≟_ (pairEqual _≟Text_ _≟Text_)

module Store = Contracts.Ownership (Maybe Owner)

data Outcome : Set where
  refused : Fault → Outcome
  reserved : Registry → Outcome

reserve : Registry → ℕ → Owner → Outcome
reserve registry identity owner with registry identity
... | nothing = reserved (Store.write identity (just owner) registry)
... | just old with ownerEqual owner old
...   | yes _ = reserved registry
...   | no _ = refused (fault [] wrongIdentity "learning item identity or provenance conflict")

after : Registry → Outcome → Registry
after registry (refused failure) = registry
after registry (reserved proposed) = proposed

noOtherItemChanges : ∀ registry identity other owner → other ≢ identity →
  after registry (reserve registry identity owner) other ≡ registry other
noOtherItemChanges registry identity other owner different with registry identity
... | nothing = Store.write-other identity other (just owner) registry different
... | just old with ownerEqual owner old
...   | yes _ = refl
...   | no _ = refl

existingOwnershipImmutable : ∀ registry identity old owner → registry identity ≡ just old →
  after registry (reserve registry identity owner) identity ≡ just old
existingOwnershipImmutable registry identity old owner original rewrite original with ownerEqual owner old
... | yes _ = original
... | no _ = original

acceptedOwnsItem : ∀ registry identity owner proposed →
  reserve registry identity owner ≡ reserved proposed → proposed identity ≡ just owner
acceptedOwnsItem registry identity owner proposed accepted with registry identity in original
... | nothing with accepted
...   | refl = Store.write-own identity (just owner) registry
acceptedOwnsItem registry identity owner proposed accepted | just old with ownerEqual owner old
... | yes refl with accepted
...   | refl = original
acceptedOwnsItem registry identity owner proposed () | just old | no _

sameOwnerIsIdempotent : ∀ registry identity owner → registry identity ≡ just owner →
  reserve registry identity owner ≡ reserved registry
sameOwnerIsIdempotent registry identity owner original rewrite original with ownerEqual owner owner
... | yes _ = refl
... | no impossible = Data.Empty.⊥-elim (impossible refl)

-- Explicit experience deletion cascades its ownership rows. Corrections do not.
deleteExperience : ℕ → Registry → Registry
deleteExperience experience registry identity with registry identity
... | nothing = nothing
... | just (owner , provenance) with owner ≟ experience
...   | yes _ = nothing
...   | no _ = just (owner , provenance)

deletedExperienceHasNoOwner : ∀ registry identity experience provenance →
  registry identity ≡ just (experience , provenance) →
  deleteExperience experience registry identity ≡ nothing
deletedExperienceHasNoOwner registry identity experience provenance original rewrite original
  with experience ≟ experience
... | yes _ = refl
... | no impossible = Data.Empty.⊥-elim (impossible refl)

otherExperienceOwnerPreserved : ∀ registry identity experience other provenance →
  registry identity ≡ just (other , provenance) → other ≢ experience →
  deleteExperience experience registry identity ≡ just (other , provenance)
otherExperienceOwnerPreserved registry identity experience other provenance original different rewrite original
  with other ≟ experience
... | yes same = Data.Empty.⊥-elim (different same)
... | no _ = refl
