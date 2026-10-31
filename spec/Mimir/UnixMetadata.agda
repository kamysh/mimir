{-# OPTIONS --safe #-}
-- The existing Unix judge-state metadata guards. Permission masks use the
-- checked bitwise-AND semantics; this adds no new filesystem policy.
module Mimir.UnixMetadata where

open import Data.Fin using (Fin; zero; toℕ; _≟_)
open import Data.Vec using ([]; _∷_; _++_; replicate)
open import Data.Nat using (ℕ; _≤_; _≤?_)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
import Data.Empty
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable.Core using (_×-dec_; _⊎-dec_; ¬?)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Mimir.Bits using (Word; O; I)
import Mimir.Bits as Bits
import Mimir.BitMaskClear as Mask

UserId = Fin (Bits.Binary.power 32)
FileSize = Fin (Bits.Binary.power 64)

data Kind : Set where directory regular symlink other : Kind

record Metadata : Set where
  constructor metadata
  field kind : Kind; owner : UserId; mode : Word 32; size : FileSize

-- 0o077, 0o022 and 0o1000 in least-significant-bit-first form.
privateMask : Word 32
privateMask = I ∷ I ∷ I ∷ I ∷ I ∷ I ∷ Mask.zeros 26

writeMask : Word 32
writeMask = O ∷ I ∷ O ∷ O ∷ I ∷ Mask.zeros 27

stickyMask : Word 32
stickyMask = replicate 9 O ++ (I ∷ Mask.zeros 22)

data IsDirectory : Kind → Set where directory : IsDirectory directory
data IsRegular : Kind → Set where regular : IsRegular regular

directory? : ∀ kind → Dec (IsDirectory kind)
directory? directory = Relation.Nullary.yes directory
directory? regular = Relation.Nullary.no (λ ())
directory? symlink = Relation.Nullary.no (λ ())
directory? other = Relation.Nullary.no (λ ())

regular? : ∀ kind → Dec (IsRegular kind)
regular? regular = Relation.Nullary.yes regular
regular? directory = Relation.Nullary.no (λ ())
regular? symlink = Relation.Nullary.no (λ ())
regular? other = Relation.Nullary.no (λ ())

Private : Metadata → Set
Private value = Mask.Clear (Metadata.mode value) privateMask

Parent : Metadata → Set
Parent value = IsDirectory (Metadata.kind value) ×
  (Mask.Clear (Metadata.mode value) writeMask ⊎
    (Metadata.owner value ≡ zero × (Mask.Clear (Metadata.mode value) stickyMask → Data.Empty.⊥)))

OwnedPrivate : UserId → Metadata → Set
OwnedPrivate user value = Metadata.owner value ≡ user × Private value

Directory : UserId → Metadata → Set
Directory user value = IsDirectory (Metadata.kind value) × OwnedPrivate user value

Lock : UserId → Metadata → Set
Lock user value = IsRegular (Metadata.kind value) × OwnedPrivate user value

Report : UserId → ℕ → Metadata → Set
Report user limit value = Lock user value × toℕ (Metadata.size value) ≤ limit

parent? : ∀ value → Dec (Parent value)
parent? value = directory? (Metadata.kind value) ×-dec
  (Mask.clear? (Metadata.mode value) writeMask ⊎-dec
    ((Metadata.owner value ≟ zero) ×-dec ¬? (Mask.clear? (Metadata.mode value) stickyMask)))

ownedPrivate? : ∀ user value → Dec (OwnedPrivate user value)
ownedPrivate? user value = (Metadata.owner value ≟ user) ×-dec Mask.clear? (Metadata.mode value) privateMask

stateDirectory? : ∀ user value → Dec (Directory user value)
stateDirectory? user value = directory? (Metadata.kind value) ×-dec ownedPrivate? user value

lock? : ∀ user value → Dec (Lock user value)
lock? user value = regular? (Metadata.kind value) ×-dec ownedPrivate? user value

report? : ∀ user limit value → Dec (Report user limit value)
report? user limit value = lock? user value ×-dec (toℕ (Metadata.size value) ≤? limit)
