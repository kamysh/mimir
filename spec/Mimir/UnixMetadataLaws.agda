{-# OPTIONS --safe #-}
-- The numeric Unix permission expressions and the independent bit predicates
-- agree for every metadata value, not just for selected permission fixtures.
module Mimir.UnixMetadataLaws where

open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Fin using (zero; toℕ)
open import Data.Nat using (ℕ; _≤_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.Bits as B
import Mimir.BitLogic as L
import Mimir.BitMaskClear as C
open import Mimir.UnixMetadata

ZeroMask : Metadata → B.Word 32 → Set
ZeroMask value mask = B.Binary.value (L.wordAnd (Metadata.mode value) mask) ≡ 0

ParentNumeric : Metadata → Set
ParentNumeric value = IsDirectory (Metadata.kind value) ×
  (ZeroMask value writeMask ⊎
    (Metadata.owner value ≡ zero × (ZeroMask value stickyMask → ⊥)))

parentComplete : ∀ {value} → Parent value → ParentNumeric value
parentComplete (kind , inj₁ clear) = kind , inj₁ (C.numericComplete clear)
parentComplete {value} (kind , inj₂ (root , sticky)) = kind ,
  inj₂ (root , λ clear → sticky (C.numericSound (Metadata.mode value) stickyMask clear))

parentSound : ∀ {value} → ParentNumeric value → Parent value
parentSound {value} (kind , inj₁ clear) = kind ,
  inj₁ (C.numericSound (Metadata.mode value) writeMask clear)
parentSound (kind , inj₂ (root , sticky)) = kind ,
  inj₂ (root , λ clear → sticky (C.numericComplete clear))

OwnedNumeric : UserId → Metadata → Set
OwnedNumeric user value = Metadata.owner value ≡ user × ZeroMask value privateMask

ownedComplete : ∀ {user value} → OwnedPrivate user value → OwnedNumeric user value
ownedComplete (owner , clear) = owner , C.numericComplete clear

ownedSound : ∀ {user value} → OwnedNumeric user value → OwnedPrivate user value
ownedSound {value = value} (owner , clear) = owner ,
  C.numericSound (Metadata.mode value) privateMask clear

DirectoryNumeric : UserId → Metadata → Set
DirectoryNumeric user value = IsDirectory (Metadata.kind value) × OwnedNumeric user value

directoryComplete : ∀ {user value} → Directory user value → DirectoryNumeric user value
directoryComplete {user} {value} (kind , owned) = kind , ownedComplete {user} {value} owned

directorySound : ∀ {user value} → DirectoryNumeric user value → Directory user value
directorySound {user} {value} (kind , owned) = kind , ownedSound {user} {value} owned

LockNumeric : UserId → Metadata → Set
LockNumeric user value = IsRegular (Metadata.kind value) × OwnedNumeric user value

lockComplete : ∀ {user value} → Lock user value → LockNumeric user value
lockComplete {user} {value} (kind , owned) = kind , ownedComplete {user} {value} owned

lockSound : ∀ {user value} → LockNumeric user value → Lock user value
lockSound {user} {value} (kind , owned) = kind , ownedSound {user} {value} owned

ReportNumeric : UserId → ℕ → Metadata → Set
ReportNumeric user limit value = LockNumeric user value × toℕ (Metadata.size value) ≤ limit

reportComplete : ∀ {user limit value} → Report user limit value → ReportNumeric user limit value
reportComplete {user} {limit} {value} (lock , size) = lockComplete {user} {value} lock , size

reportSound : ∀ {user limit value} → ReportNumeric user limit value → Report user limit value
reportSound {user} {limit} {value} (lock , size) = lockSound {user} {value} lock , size
