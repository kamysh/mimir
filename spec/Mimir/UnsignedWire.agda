{-# OPTIONS --safe #-}
-- Integer wire conversion preserves bounds and rejects floating encodings,
-- including a floating-point value that happens to have an integer magnitude.
module Mimir.UnsignedWire where

open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties using (fromℕ<-toℕ; toℕ<n)
open import Data.Nat using (ℕ; suc; _≤_; _≤?_; s≤s; s≤s⁻¹)
open import Data.Product using (Σ; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Mimir.StructuredValue
open import Mimir.RecordDecoding using (mapResult)
open import Mimir.Validation

natural : ℕ → Value → Fault ⊎ ℕ
natural maximum raw = mapResult proj₁ (result (uint maximum raw))

naturalRoundTrip : ∀ maximum n → n ≤ maximum → natural maximum (unsigned n) ≡ inj₂ n
naturalRoundTrip maximum n bounded with n ≤? maximum
... | yes _ = refl
... | no tooLarge = ⊥-elim (tooLarge bounded)

naturalBounded : ∀ maximum raw n → natural maximum raw ≡ inj₂ n → n ≤ maximum
naturalBounded maximum raw n proof with uint maximum raw
... | rejected failure invalid with proof
...   | ()
naturalBounded maximum raw n proof | accepted (number , witness) with proof
... | refl = integerInRange witness

finite : (maximum : ℕ) → Value → Fault ⊎ Fin (suc maximum)
finite maximum raw with uint maximum raw
... | rejected failure invalid = inj₁ failure
... | accepted (number , witness) = inj₂ (fromℕ< (s≤s (integerInRange witness)))

finiteRoundTrip : ∀ maximum (number : Fin (suc maximum)) →
  finite maximum (unsigned (toℕ number)) ≡ inj₂ number
finiteRoundTrip maximum number with toℕ number ≤? maximum
... | yes bounded = cong inj₂ (fromℕ<-toℕ number (s≤s bounded))
... | no tooLarge = ⊥-elim (tooLarge (s≤s⁻¹ (toℕ<n number)))
