{-# OPTIONS --safe #-}
-- Exact-length byte arrays at database/wire boundaries. No padding,
-- truncation, or unchecked conversion is admitted.
module Mimir.ExactBytes where

open import Data.Fin using (Fin)
open import Data.List using (List; length)
open import Data.Nat using (ℕ; _≟_)
open import Data.Vec using (Vec; fromList; toList)
open import Data.Vec.Properties using (toList∘fromList; length-toList; ≡-dec)
import Data.Fin.Properties as Fin
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong)

Byte = Fin 256
Bytes : ℕ → Set
Bytes = Vec Byte

data Read (size : ℕ) (input : List Byte) : Set where
  accepted : (bytes : Bytes size) → toList bytes ≡ input → Read size input
  wrongLength : ¬ (length input ≡ size) → Read size input

castBytes : ∀ size (input : List Byte) → length input ≡ size → Bytes size
castBytes .(length input) input refl = fromList input

castExact : ∀ size input (exact : length input ≡ size) → toList (castBytes size input exact) ≡ input
castExact .(length input) input refl = toList∘fromList input

read : ∀ size input → Read size input
read size input with length input ≟ size
... | yes exact = accepted (castBytes size input exact) (castExact size input exact)
... | no different = wrongLength different

acceptedLength : ∀ size input (bytes : Bytes size) → toList bytes ≡ input → length input ≡ size
acceptedLength size input bytes exact = trans (sym (cong length exact)) (length-toList bytes)

equal : ∀ {size} → DecidableEquality (Bytes size)
equal = ≡-dec Fin._≟_
