{-# OPTIONS --safe #-}
-- uuid 1.28.0 nibble decoding uses wrapping u8 subtraction and OR 0x20.
-- Exhaustive finite proofs cover every byte, not selected regression inputs.
module Mimir.UUIDHexClassifier where

open import Data.Fin using (toℕ)
import Data.Fin.Properties as Fin
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Properties as Maybe
open import Data.Nat using (ℕ; _+_; _∸_; _%_; _<?_; _≟_)
open import Data.Unit using (tt)
import Data.Vec as V
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Mimir.Bits using (Byte; Word; O; I)
import Mimir.Bits as Bits
import Mimir.BitLogic as Logic
import Mimir.WordEncoding as Word
import Mimir.HexEscape as Hex

mask32 : Word 8
mask32 = O V.∷ O V.∷ O V.∷ O V.∷ O V.∷ I V.∷ O V.∷ O V.∷ V.[]

subtract8 : ℕ → ℕ → ℕ
subtract8 number amount = (number + 256 ∸ amount) % 256

caseFold : Byte → ℕ
caseFold byte = Bits.Binary.value (Logic.wordOr (Word.encode 8 (toℕ byte)) mask32)

select : ℕ → ℕ → Maybe ℕ
select digit alpha with digit <? 10
... | yes digitRange = just digit
... | no notDigit with alpha <? 6
...   | yes alphaRange = just ((alpha + 10) % 256)
...   | no notAlpha = nothing

native : Byte → Maybe ℕ
native byte = select (subtract8 (toℕ byte) 48) (subtract8 (caseFold byte) 97)

reference : Byte → Maybe ℕ
reference byte with Hex.read byte
... | yes value = just (toℕ (Hex.number (Hex.ReadDigit.digit value)))
... | no invalid = nothing

abstract
  nativeCorrect : ∀ byte → native byte ≡ reference byte
  nativeCorrect = toWitness {a? = Fin.all? (λ byte → Maybe.≡-dec _≟_ (native byte) (reference byte))} tt
