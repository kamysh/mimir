{-# OPTIONS --safe #-}
-- Correspondence with uuid 1.28.0 nibble_to_hex for its lowercase JSON path.
module Mimir.UUIDLowerFormatting where

open import Data.Fin using (Fin; toℕ)
import Data.Fin.Properties as Fin
open import Data.Nat using (ℕ; _+_; _<?_; _≟_)
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Mimir.HexEscape as Hex

native : Fin 16 → ℕ
native digit with 9 <? toℕ digit
... | yes alpha = toℕ digit + 48 + 39
... | no decimal = toℕ digit + 48

abstract
  lowerExact : ∀ digit → native digit ≡ toℕ (Hex.byte (Hex.lowerDigit digit))
  lowerExact = toWitness {a? = Fin.all? (λ digit → native digit ≟ toℕ (Hex.byte (Hex.lowerDigit digit)))} tt
