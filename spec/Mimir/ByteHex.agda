{-# OPTIONS --safe #-}
-- Two hexadecimal digits per byte, high nibble first. Parsing accepts both
-- ASCII cases; encoding is canonical lowercase and preserves every byte.
module Mimir.ByteHex where

open import Data.Fin using (Fin; toℕ; fromℕ<)
open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ-injective)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Properties
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Mimir.Bits using (Byte)
import Mimir.HexEscape as Hex
import Mimir.LowerHex as Lower

assemble : Vec (Fin 16) 2 → Byte
assemble digits = fromℕ< (Lower.Hex.valueBound digits)

assembleExact : ∀ byte → assemble (Lower.digits byte) ≡ byte
assembleExact byte = toℕ-injective (trans (toℕ-fromℕ< (Lower.Hex.valueBound (Lower.digits byte))) (Lower.digitsValue byte))

spellDigits : Vec (Fin 16) 2 → Vec Byte 2
spellDigits (low ∷ high ∷ []) = Hex.byte (Hex.lowerDigit high) ∷ Hex.byte (Hex.lowerDigit low) ∷ []

pair : Byte → Vec Byte 2
pair byte = spellDigits (Lower.digits byte)

decode : Byte → Byte → Maybe Byte
decode high low with Hex.read high
... | no invalid = nothing
... | yes (Hex.readDigit highDigit highExact) with Hex.read low
...   | no invalid = nothing
...   | yes (Hex.readDigit lowDigit lowExact) = just (assemble (Hex.number lowDigit ∷ Hex.number highDigit ∷ []))

decodePair : Vec Byte 2 → Maybe Byte
decodePair (high ∷ low ∷ []) = decode high low

lowerRoundTrip : ∀ high low → decode (Hex.byte (Hex.lowerDigit high)) (Hex.byte (Hex.lowerDigit low)) ≡ just (assemble (low ∷ high ∷ []))
lowerRoundTrip high low rewrite Hex.readComplete (Hex.lowerDigit high) | Hex.readComplete (Hex.lowerDigit low) |
  Hex.lowerDigitValue high | Hex.lowerDigitValue low = refl

digitsRoundTrip : ∀ digits → decodePair (spellDigits digits) ≡ just (assemble digits)
digitsRoundTrip (low ∷ high ∷ []) = lowerRoundTrip high low

roundTrip : ∀ byte → decodePair (pair byte) ≡ just byte
roundTrip byte = trans (digitsRoundTrip (Lower.digits byte)) (cong just (assembleExact byte))

pairInjective : ∀ first second → pair first ≡ pair second → first ≡ second
pairInjective first second same = Data.Maybe.Properties.just-injective
  (trans (Relation.Binary.PropositionalEquality.sym (roundTrip first)) (trans (cong decodePair same) (roundTrip second)))
