{-# OPTIONS --safe #-}
-- JSON hexadecimal escapes over actual wire bytes. Both ASCII letter cases
-- are accepted. The SliceRead path consumes four bytes before checking them.
module Mimir.HexEscape where

open import Data.Fin using (Fin; #_; toℕ; _≟_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_; _*_; _≤_; _<_; z≤n; s≤s)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Relation.Nullary using (Dec)
import Data.Vec as Vec
import Data.Fin as Fin
open import Data.Fin.Properties using (toℕ-injective)
open import Data.Nat.Properties using (+-identityʳ)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Mimir.Bits using (Byte; Word)
import Mimir.Bits as Bits
import Mimir.UTF16Escape as U

data Digit : Set where
  h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 upperA upperB upperC upperD upperE upperF lowerA lowerB lowerC lowerD lowerE lowerF : Digit

byte : Digit → Byte
byte h0 = # 48
byte h1 = # 49
byte h2 = # 50
byte h3 = # 51
byte h4 = # 52
byte h5 = # 53
byte h6 = # 54
byte h7 = # 55
byte h8 = # 56
byte h9 = # 57
byte upperA = # 65
byte upperB = # 66
byte upperC = # 67
byte upperD = # 68
byte upperE = # 69
byte upperF = # 70
byte lowerA = # 97
byte lowerB = # 98
byte lowerC = # 99
byte lowerD = # 100
byte lowerE = # 101
byte lowerF = # 102

number : Digit → Fin 16
number h0 = # 0
number h1 = # 1
number h2 = # 2
number h3 = # 3
number h4 = # 4
number h5 = # 5
number h6 = # 6
number h7 = # 7
number h8 = # 8
number h9 = # 9
number upperA = # 10
number upperB = # 11
number upperC = # 12
number upperD = # 13
number upperE = # 14
number upperF = # 15
number lowerA = # 10
number lowerB = # 11
number lowerC = # 12
number lowerD = # 13
number lowerE = # 14
number lowerF = # 15

record ReadDigit (input : Byte) : Set where
  constructor readDigit
  field digit : Digit; spelling : input ≡ byte digit

find : ∀ input candidates → Dec (Any (λ digit → input ≡ byte digit) candidates)
find input [] = no (λ ())
find input (digit ∷ rest) with input ≟ byte digit
... | yes same = yes (here same)
... | no different with find input rest
...   | yes found = yes (there found)
...   | no missing = no λ { (here same) → different same ; (there found) → missing found }

extract : ∀ {input candidates} → Any (λ digit → input ≡ byte digit) candidates → ReadDigit input
extract {candidates = digit ∷ rest} (here same) = readDigit digit same
extract (there found) = extract found

candidates : List Digit
candidates = h0 ∷ h1 ∷ h2 ∷ h3 ∷ h4 ∷ h5 ∷ h6 ∷ h7 ∷ h8 ∷ h9 ∷ upperA ∷ upperB ∷ upperC ∷ upperD ∷ upperE ∷ upperF ∷ lowerA ∷ lowerB ∷ lowerC ∷ lowerD ∷ lowerE ∷ lowerF ∷ []

included : ∀ digit → Any (λ candidate → byte digit ≡ byte candidate) candidates
included h0 = here refl
included h1 = there (here refl)
included h2 = there (there (here refl))
included h3 = there (there (there (here refl)))
included h4 = there (there (there (there (here refl))))
included h5 = there (there (there (there (there (here refl)))))
included h6 = there (there (there (there (there (there (here refl))))))
included h7 = there (there (there (there (there (there (there (here refl)))))))
included h8 = there (there (there (there (there (there (there (there (here refl))))))))
included h9 = there (there (there (there (there (there (there (there (there (here refl)))))))))
included upperA = there (there (there (there (there (there (there (there (there (there (here refl))))))))))
included upperB = there (there (there (there (there (there (there (there (there (there (there (here refl)))))))))))
included upperC = there (there (there (there (there (there (there (there (there (there (there (there (here refl))))))))))))
included upperD = there (there (there (there (there (there (there (there (there (there (there (there (there (here refl)))))))))))))
included upperE = there (there (there (there (there (there (there (there (there (there (there (there (there (there (here refl))))))))))))))
included upperF = there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here refl)))))))))))))))
included lowerA = there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here refl))))))))))))))))
included lowerB = there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here refl)))))))))))))))))
included lowerC = there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here refl))))))))))))))))))
included lowerD = there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here refl)))))))))))))))))))
included lowerE = there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here refl))))))))))))))))))))
included lowerF = there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here refl)))))))))))))))))))))

read : ∀ input → Dec (ReadDigit input)
read input with find input candidates
... | yes found = yes (extract found)
... | no missing = no λ { (readDigit digit refl) → missing (included digit) }

readComplete : ∀ digit → read (byte digit) ≡ yes (readDigit digit refl)
readComplete h0 = refl
readComplete h1 = refl
readComplete h2 = refl
readComplete h3 = refl
readComplete h4 = refl
readComplete h5 = refl
readComplete h6 = refl
readComplete h7 = refl
readComplete h8 = refl
readComplete h9 = refl
readComplete upperA = refl
readComplete upperB = refl
readComplete upperC = refl
readComplete upperD = refl
readComplete upperE = refl
readComplete upperF = refl
readComplete lowerA = refl
readComplete lowerB = refl
readComplete lowerC = refl
readComplete lowerD = refl
readComplete lowerE = refl
readComplete lowerF = refl

record Four : Set where
  constructor four
  field first second third fourth : Digit

spell : Four → List Byte
spell (four a b c d) = byte a ∷ byte b ∷ byte c ∷ byte d ∷ []

unit : Four → U.Unit
unit (four a b c d) = Bits.unpack 4 (number d) Vec.++
  (Bits.unpack 4 (number c) Vec.++ (Bits.unpack 4 (number b) Vec.++ Bits.unpack 4 (number a)))

numeric : Four → ℕ
numeric (four a b c d) = toℕ (number d) +
  (toℕ (number c) + (toℕ (number b) + toℕ (number a) * 16) * 16) * 16

unitValue : ∀ digits → U.value (unit digits) ≡ numeric digits
unitValue (four a b c d)
  rewrite Bits.Binary.valueAppend (Bits.unpack 4 (number d))
      (Bits.unpack 4 (number c) Vec.++ (Bits.unpack 4 (number b) Vec.++ Bits.unpack 4 (number a))) |
    Bits.Binary.valueAppend (Bits.unpack 4 (number c))
      (Bits.unpack 4 (number b) Vec.++ Bits.unpack 4 (number a)) |
    Bits.Binary.valueAppend (Bits.unpack 4 (number b)) (Bits.unpack 4 (number a)) |
    Bits.unpackValue 4 (number a) | Bits.unpackValue 4 (number b) |
    Bits.unpackValue 4 (number c) | Bits.unpackValue 4 (number d) = refl

record Parsed (input : List Byte) : Set where
  constructor parsed
  field digits : Four; rest : List Byte; exact : input ≡ spell digits ++ rest

data Failure (input : List Byte) : Set where
  truncated : length input < 4 → Failure input
  invalid : ∀ a b c d rest → input ≡ a ∷ b ∷ c ∷ d ∷ rest →
    ((ReadDigit a → ⊥) ⊎ ((ReadDigit b → ⊥) ⊎ ((ReadDigit c → ⊥) ⊎ (ReadDigit d → ⊥)))) → Failure input

parse : ∀ input → Failure input ⊎ Parsed input
parse [] = inj₁ (truncated (s≤s z≤n))
parse (a ∷ []) = inj₁ (truncated (s≤s (s≤s z≤n)))
parse (a ∷ b ∷ []) = inj₁ (truncated (s≤s (s≤s (s≤s z≤n))))
parse (a ∷ b ∷ c ∷ []) = inj₁ (truncated (s≤s (s≤s (s≤s (s≤s z≤n)))))
parse (a ∷ b ∷ c ∷ d ∷ rest) with read a
... | no rejected = inj₁ (invalid a b c d rest refl (inj₁ rejected))
... | yes (readDigit da sameA) with read b
...   | no rejected = inj₁ (invalid a b c d rest refl (inj₂ (inj₁ rejected)))
...   | yes (readDigit db sameB) with read c
...     | no rejected = inj₁ (invalid a b c d rest refl (inj₂ (inj₂ (inj₁ rejected))))
...     | yes (readDigit dc sameC) with read d
...       | no rejected = inj₁ (invalid a b c d rest refl (inj₂ (inj₂ (inj₂ rejected))))
...       | yes (readDigit dd sameD) rewrite sameA | sameB | sameC | sameD =
          inj₂ (parsed (four da db dc dd) rest refl)

parseComplete : ∀ digits rest → parse (spell digits ++ rest) ≡ inj₂ (parsed digits rest refl)
parseComplete (four a b c d) rest
  rewrite readComplete a | readComplete b | readComplete c | readComplete d = refl

consumed : ∀ {input} → Failure input → ℕ
consumed {input} (truncated _) = length input
consumed (invalid a b c d rest same rejection) = 4

validNotFailure : ∀ digits rest → Failure (spell digits ++ rest) → ⊥
validNotFailure (four a b c d) rest (truncated (s≤s (s≤s (s≤s (s≤s ())))))
validNotFailure (four a b c d) rest (invalid _ _ _ _ _ refl (inj₁ rejected)) = rejected (readDigit a refl)
validNotFailure (four a b c d) rest (invalid _ _ _ _ _ refl (inj₂ (inj₁ rejected))) = rejected (readDigit b refl)
validNotFailure (four a b c d) rest (invalid _ _ _ _ _ refl (inj₂ (inj₂ (inj₁ rejected)))) = rejected (readDigit c refl)
validNotFailure (four a b c d) rest (invalid _ _ _ _ _ refl (inj₂ (inj₂ (inj₂ rejected)))) = rejected (readDigit d refl)

-- Canonical lowercase hexadecimal spelling used by JSON serialization.
lowerDigit : Fin 16 → Digit
lowerDigit Fin.zero = h0
lowerDigit (Fin.suc (Fin.zero)) = h1
lowerDigit (Fin.suc (Fin.suc (Fin.zero))) = h2
lowerDigit (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))) = h3
lowerDigit (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))) = h4
lowerDigit (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))) = h5
lowerDigit (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))) = h6
lowerDigit (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))) = h7
lowerDigit (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))) = h8
lowerDigit (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))))) = h9
lowerDigit (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))))) = lowerA
lowerDigit (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))))))) = lowerB
lowerDigit (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))))))) = lowerC
lowerDigit (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))))))))) = lowerD
lowerDigit (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))))))))) = lowerE
lowerDigit (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))))))))))) = lowerF

lowerDigitValue : ∀ value → number (lowerDigit value) ≡ value
lowerDigitValue Fin.zero = refl
lowerDigitValue (Fin.suc (Fin.zero)) = refl
lowerDigitValue (Fin.suc (Fin.suc (Fin.zero))) = refl
lowerDigitValue (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))) = refl
lowerDigitValue (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))) = refl
lowerDigitValue (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))) = refl
lowerDigitValue (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))) = refl
lowerDigitValue (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))) = refl
lowerDigitValue (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))) = refl
lowerDigitValue (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))))) = refl
lowerDigitValue (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))))) = refl
lowerDigitValue (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))))))) = refl
lowerDigitValue (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))))))) = refl
lowerDigitValue (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))))))))) = refl
lowerDigitValue (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))))))))) = refl
lowerDigitValue (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))))))))))) = refl

fromUnit : U.Unit → Four
fromUnit (d0 Vec.∷ d1 Vec.∷ d2 Vec.∷ d3 Vec.∷ c0 Vec.∷ c1 Vec.∷ c2 Vec.∷ c3 Vec.∷ b0 Vec.∷ b1 Vec.∷ b2 Vec.∷ b3 Vec.∷ a0 Vec.∷ a1 Vec.∷ a2 Vec.∷ a3 Vec.∷ Vec.[]) =
  four (lowerDigit (Bits.pack (a0 Vec.∷ a1 Vec.∷ a2 Vec.∷ a3 Vec.∷ Vec.[]))) (lowerDigit (Bits.pack (b0 Vec.∷ b1 Vec.∷ b2 Vec.∷ b3 Vec.∷ Vec.[]))) (lowerDigit (Bits.pack (c0 Vec.∷ c1 Vec.∷ c2 Vec.∷ c3 Vec.∷ Vec.[]))) (lowerDigit (Bits.pack (d0 Vec.∷ d1 Vec.∷ d2 Vec.∷ d3 Vec.∷ Vec.[])))

fromUnitExact : ∀ value → unit (fromUnit value) ≡ value
fromUnitExact (d0 Vec.∷ d1 Vec.∷ d2 Vec.∷ d3 Vec.∷ c0 Vec.∷ c1 Vec.∷ c2 Vec.∷ c3 Vec.∷ b0 Vec.∷ b1 Vec.∷ b2 Vec.∷ b3 Vec.∷ a0 Vec.∷ a1 Vec.∷ a2 Vec.∷ a3 Vec.∷ Vec.[])
  rewrite lowerDigitValue (Bits.pack (a0 Vec.∷ a1 Vec.∷ a2 Vec.∷ a3 Vec.∷ Vec.[])) |
    lowerDigitValue (Bits.pack (b0 Vec.∷ b1 Vec.∷ b2 Vec.∷ b3 Vec.∷ Vec.[])) |
    lowerDigitValue (Bits.pack (c0 Vec.∷ c1 Vec.∷ c2 Vec.∷ c3 Vec.∷ Vec.[])) |
    lowerDigitValue (Bits.pack (d0 Vec.∷ d1 Vec.∷ d2 Vec.∷ d3 Vec.∷ Vec.[])) |
    Bits.unpackPack (a0 Vec.∷ a1 Vec.∷ a2 Vec.∷ a3 Vec.∷ Vec.[]) |
    Bits.unpackPack (b0 Vec.∷ b1 Vec.∷ b2 Vec.∷ b3 Vec.∷ Vec.[]) |
    Bits.unpackPack (c0 Vec.∷ c1 Vec.∷ c2 Vec.∷ c3 Vec.∷ Vec.[]) |
    Bits.unpackPack (d0 Vec.∷ d1 Vec.∷ d2 Vec.∷ d3 Vec.∷ Vec.[]) = refl

zeroNibble : Word 4
zeroNibble = Bits.O Vec.∷ Bits.O Vec.∷ Bits.O Vec.∷ Bits.O Vec.∷ Vec.[]

zeroByte : Word 8
zeroByte = zeroNibble Vec.++ zeroNibble

abstract
  packZeroNibble : Bits.pack zeroNibble ≡ Fin.zero
  packZeroNibble = toℕ-injective (Bits.packValue zeroNibble)

byteUnit : Word 8 → U.Unit
byteUnit word = word Vec.++ zeroByte

byteUnitValue : ∀ word → U.value (byteUnit word) ≡ Bits.Binary.value word
byteUnitValue word rewrite Bits.Binary.valueAppend word zeroByte = +-identityʳ (Bits.Binary.value word)

byteUnitPrefix : ∀ word → Four.first (fromUnit (byteUnit word)) ≡ h0 × Four.second (fromUnit (byteUnit word)) ≡ h0
byteUnitPrefix (a Vec.∷ b Vec.∷ c Vec.∷ d Vec.∷ e Vec.∷ f Vec.∷ g Vec.∷ h Vec.∷ Vec.[])
  rewrite packZeroNibble = refl , refl
