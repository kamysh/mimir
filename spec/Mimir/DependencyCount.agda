{-# OPTIONS --safe #-}
-- Semantic indegree counts duplicate requirements separately, just as the
-- reverse-edge vectors in Kryzhen do. Zero is equivalent to readiness.
module Mimir.DependencyCount where

open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _+_; _∸_)
open import Data.Nat.Properties using (m≤n⇒m≤1+n; +-suc; m≤m+n; m+n∸m≡n)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym; subst)
open import Mimir.Collections using (module Equality)

module Count (Name : Set) (equal : DecidableEquality Name) where
  module Names = Equality Name equal

  unmet : List Name → List Name → ℕ
  unmet completed [] = zero
  unmet completed (dependency ∷ rest) with Names.present? dependency completed
  ... | yes found = unmet completed rest
  ... | no absent = suc (unmet completed rest)

  Ready : List Name → List Name → Set
  Ready completed requirements = All (λ dependency → dependency ∈ completed) requirements

  zeroIsReady : ∀ completed requirements → unmet completed requirements ≡ zero → Ready completed requirements
  zeroIsReady completed [] same = []
  zeroIsReady completed (dependency ∷ rest) same with Names.present? dependency completed
  ... | yes found = found ∷ zeroIsReady completed rest same
  ... | no absent with same
  ...   | ()

  readyIsZero : ∀ completed requirements → Ready completed requirements → unmet completed requirements ≡ zero
  readyIsZero completed [] [] = refl
  readyIsZero completed (dependency ∷ rest) (found ∷ remaining) with Names.present? dependency completed
  ... | yes present = readyIsZero completed rest remaining
  ... | no absent = ⊥-elim (absent found)

  boundedByRequirements : ∀ completed requirements → unmet completed requirements ≤ length requirements
  boundedByRequirements completed [] = z≤n
  boundedByRequirements completed (dependency ∷ rest) with Names.present? dependency completed
  ... | yes found = m≤n⇒m≤1+n (boundedByRequirements completed rest)
  ... | no absent = s≤s (boundedByRequirements completed rest)

  -- Repeated dependency names contribute repeated incoming edges. This is
  -- needed when relating count updates to the source's dependents Vec.
  occurrences : Name → List Name → ℕ
  occurrences selected [] = zero
  occurrences selected (dependency ∷ rest) with equal dependency selected
  ... | yes same = suc (occurrences selected rest)
  ... | no different = occurrences selected rest

  skipPresent : ∀ completed dependency rest → dependency ∈ completed →
    unmet completed (dependency ∷ rest) ≡ unmet completed rest
  skipPresent completed dependency rest found with Names.present? dependency completed
  ... | yes present = refl
  ... | no absent = ⊥-elim (absent found)

  countAbsent : ∀ completed dependency rest → ¬ (dependency ∈ completed) →
    unmet completed (dependency ∷ rest) ≡ suc (unmet completed rest)
  countAbsent completed dependency rest absent with Names.present? dependency completed
  ... | yes found = ⊥-elim (absent found)
  ... | no missing = refl

  occurrencesSame : ∀ selected rest → occurrences selected (selected ∷ rest) ≡ suc (occurrences selected rest)
  occurrencesSame selected rest with equal selected selected
  ... | yes same = refl
  ... | no different = ⊥-elim (different refl)

  occurrencesOther : ∀ selected dependency rest → dependency ≢ selected →
    occurrences selected (dependency ∷ rest) ≡ occurrences selected rest
  occurrencesOther selected dependency rest different with equal dependency selected
  ... | yes same = ⊥-elim (different same)
  ... | no unequal = refl

  absentAfter : ∀ (selected : Name) (completed : List Name) (dependency : Name) → dependency ≢ selected →
    ¬ (dependency ∈ completed) → ¬ (dependency ∈ selected ∷ completed)
  absentAfter selected completed dependency different absent (here same) = different same
  absentAfter selected completed dependency different absent (there found) = absent found

  contributionRemoved : ∀ selected completed requirements → ¬ (selected ∈ completed) →
    unmet completed requirements ≡ occurrences selected requirements + unmet (selected ∷ completed) requirements
  contributionRemoved selected completed [] fresh = refl
  contributionRemoved selected completed (dependency ∷ rest) fresh with equal dependency selected
  ... | yes refl rewrite countAbsent completed selected rest fresh =
      cong suc (contributionRemoved selected completed rest fresh)
  ... | no different with Names.present? dependency completed
  ...   | yes found = contributionRemoved selected completed rest fresh
  ...   | no absent =
      trans (cong suc (contributionRemoved selected completed rest fresh))
        (sym (+-suc (occurrences selected rest) (unmet (selected ∷ completed) rest)))

  removalCannotUnderflow : ∀ selected completed requirements → ¬ (selected ∈ completed) →
    occurrences selected requirements ≤ unmet completed requirements
  removalCannotUnderflow selected completed requirements fresh =
    subst (occurrences selected requirements ≤_) (sym (contributionRemoved selected completed requirements fresh))
      (m≤m+n (occurrences selected requirements) (unmet (selected ∷ completed) requirements))

  subtractionIsExact : ∀ selected completed requirements → ¬ (selected ∈ completed) →
    unmet completed requirements ∸ occurrences selected requirements ≡ unmet (selected ∷ completed) requirements
  subtractionIsExact selected completed requirements fresh =
    trans (cong (_∸ occurrences selected requirements) (contributionRemoved selected completed requirements fresh))
      (m+n∸m≡n (occurrences selected requirements) (unmet (selected ∷ completed) requirements))

  presentAfter : ∀ selected completed requirements →
    Ready completed requirements → Ready (selected ∷ completed) requirements
  presentAfter selected completed [] [] = []
  presentAfter selected completed (dependency ∷ rest) (found ∷ remaining) =
    there found ∷ presentAfter selected completed rest remaining

  completingCannotDisable : ∀ selected completed requirements →
    unmet completed requirements ≡ zero → unmet (selected ∷ completed) requirements ≡ zero
  completingCannotDisable selected completed requirements same =
    readyIsZero (selected ∷ completed) requirements
      (presentAfter selected completed requirements (zeroIsReady completed requirements same))
