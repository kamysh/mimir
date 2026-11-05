{-# OPTIONS --safe #-}
-- The two Kryzhen admission passes, with first-error witnesses. Equality
-- decisions are supplied with proofs; they are not unchecked Boolean oracles.
module Mimir.MigrationValidation where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Validate (Name Checksum : Set)
  (nameEqual : DecidableEquality Name) (checksumEqual : DecidableEquality Checksum) where

  member? : ∀ (name : Name) names → Dec (name ∈ names)
  member? name [] = no (λ ())
  member? name (other ∷ rest) with nameEqual name other
  ... | yes same = yes (here same)
  ... | no different with member? name rest
  ...   | yes found = yes (there found)
  ...   | no absent = no λ where
    (here same) → different same
    (there found) → absent found

  data Fresh : List Name → List Name → Set where
    empty : ∀ seen → Fresh seen []
    next : ∀ {seen name rest} → ¬ (name ∈ seen) →
      Fresh (name ∷ seen) rest → Fresh seen (name ∷ rest)

  data FirstDuplicate : List Name → List Name → Set where
    duplicate : ∀ {seen name rest} → name ∈ seen → FirstDuplicate seen (name ∷ rest)
    later : ∀ {seen name rest} → ¬ (name ∈ seen) →
      FirstDuplicate (name ∷ seen) rest → FirstDuplicate seen (name ∷ rest)

  duplicateName : ∀ {seen names} → FirstDuplicate seen names → Name
  duplicateName (duplicate {name = name} _) = name
  duplicateName (later _ laterDuplicate) = duplicateName laterDuplicate

  inspectNames : ∀ seen names → FirstDuplicate seen names ⊎ Fresh seen names
  inspectNames seen [] = inj₂ (empty seen)
  inspectNames seen (name ∷ rest) with member? name seen
  ... | yes found = inj₁ (duplicate found)
  ... | no absent with inspectNames (name ∷ seen) rest
  ...   | inj₁ failure = inj₁ (later absent failure)
  ...   | inj₂ fresh = inj₂ (next absent fresh)

  noDuplicateWhenFresh : ∀ {seen names} → Fresh seen names → FirstDuplicate seen names → ⊥
  noDuplicateWhenFresh (next absent _) (duplicate found) = absent found
  noDuplicateWhenFresh (next _ fresh) (later _ repeated) = noDuplicateWhenFresh fresh repeated

  -- This projection has the source's Result<()>, reporting the earliest
  -- repeated name in input order. The inspectNames witness is retained above.
  checkNames : List Name → Name ⊎ ⊤
  checkNames names with inspectNames [] names
  ... | inj₁ failure = inj₁ (duplicateName failure)
  ... | inj₂ fresh = inj₂ tt

  namesSound : ∀ names → checkNames names ≡ inj₂ tt → Fresh [] names
  namesSound names with inspectNames [] names
  ... | inj₁ failure = λ ()
  ... | inj₂ fresh = λ _ → fresh

  namesComplete : ∀ names → Fresh [] names → checkNames names ≡ inj₂ tt
  namesComplete names fresh with inspectNames [] names
  ... | inj₁ failure = ⊥-elim (noDuplicateWhenFresh fresh failure)
  ... | inj₂ valid = refl

  Entry = Name × Checksum
  Stored = Name → Maybe Checksum

  Compatible : Stored → Entry → Set
  Compatible stored (name , checksum) with stored name
  ... | nothing = ⊤
  ... | just previous = previous ≡ checksum

  compatible? : ∀ stored entry → Dec (Compatible stored entry)
  compatible? stored (name , checksum) with stored name
  ... | nothing = yes tt
  ... | just previous = checksumEqual previous checksum

  data FirstMismatch (stored : Stored) : List Entry → Set where
    mismatch : ∀ {entry rest} → ¬ Compatible stored entry → FirstMismatch stored (entry ∷ rest)
    later : ∀ {entry rest} → Compatible stored entry →
      FirstMismatch stored rest → FirstMismatch stored (entry ∷ rest)

  mismatchedName : ∀ {stored entries} → FirstMismatch stored entries → Name
  mismatchedName (mismatch {entry = name , _} _) = name
  mismatchedName (later _ laterMismatch) = mismatchedName laterMismatch

  inspectChecksums : ∀ stored entries →
    FirstMismatch stored entries ⊎ All (Compatible stored) entries
  inspectChecksums stored [] = inj₂ []
  inspectChecksums stored (entry ∷ rest) with compatible? stored entry
  ... | no different = inj₁ (mismatch different)
  ... | yes matches with inspectChecksums stored rest
  ...   | inj₁ failure = inj₁ (later matches failure)
  ...   | inj₂ valid = inj₂ (matches ∷ valid)

  noMismatchWhenCompatible : ∀ {stored entries} →
    All (Compatible stored) entries → FirstMismatch stored entries → ⊥
  noMismatchWhenCompatible (matches ∷ _) (mismatch different) = different matches
  noMismatchWhenCompatible (_ ∷ valid) (later _ failure) = noMismatchWhenCompatible valid failure

  checkChecksums : Stored → List Entry → Name ⊎ ⊤
  checkChecksums stored entries with inspectChecksums stored entries
  ... | inj₁ failure = inj₁ (mismatchedName failure)
  ... | inj₂ valid = inj₂ tt

  checksumsSound : ∀ stored entries → checkChecksums stored entries ≡ inj₂ tt →
    All (Compatible stored) entries
  checksumsSound stored entries with inspectChecksums stored entries
  ... | inj₁ failure = λ ()
  ... | inj₂ valid = λ _ → valid

  checksumsComplete : ∀ stored entries → All (Compatible stored) entries →
    checkChecksums stored entries ≡ inj₂ tt
  checksumsComplete stored entries valid with inspectChecksums stored entries
  ... | inj₁ failure = ⊥-elim (noMismatchWhenCompatible valid failure)
  ... | inj₂ accepted = refl
