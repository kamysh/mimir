{-# OPTIONS --safe #-}
-- Numeric token and diagnostic types shared with application decoding.
-- Floating conversion is supplied through a separate dependency interface.
module Mimir.NumericTokens where

open import Data.Char using (Char; _≟_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _+_; _*_; _≤_; _≤?_; s≤s; z≤n)
import Data.Nat as Nat
open import Data.Nat.Properties using (≤-trans)
open import Data.Integer using (ℤ; +_)
import Data.Integer as Int
open import Data.Fin using (Fin; fromℕ<)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.Binary64 using (Sign; positive; negative; power; powerMinusOne)
import Mimir.FloatValue as A
import Mimir.DecimalLexer as Digits
import Mimir.Unsigned as D
import Mimir.SignedMachine as Machine
import Mimir.SignedMagnitude as Magnitude
import Mimir.SequenceCursor as Cursor

module I32 = Machine.Width 31
module I64 = Machine.Width 63

U64 : Set
U64 = D.UInt (powerMinusOne 64)

Exponent : Set
Exponent = D.UInt (powerMinusOne 31)

digitBound : ∀ digit → D.value digit ≤ 9
digitBound D.d0 = z≤n
digitBound D.d1 = s≤s z≤n
digitBound D.d2 = s≤s (s≤s z≤n)
digitBound D.d3 = s≤s (s≤s (s≤s z≤n))
digitBound D.d4 = s≤s (s≤s (s≤s (s≤s z≤n)))
digitBound D.d5 = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))
digitBound D.d6 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
digitBound D.d7 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))
digitBound D.d8 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))
digitBound D.d9 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))

digit64 : D.Digit → U64
digit64 digit = D.uint (D.value digit) (≤-trans (digitBound digit)
  (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))

digitExponent : D.Digit → Exponent
digitExponent digit = D.uint (D.value digit) (≤-trans (digitBound digit)
  (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))

asFin : U64 → Fin (power 64)
asFin number = fromℕ< (s≤s (D.UInt.bounded number))

abstract
  zeroCounter : I32.Integer
  zeroCounter = I32.wrap (+ 0)

  signedInteger : U64 → I64.Integer
  signedInteger number = I64.wrap (Int.- I64.Integer.number (I64.wrap (+ D.UInt.number number)))

  signedIntegerExact : ∀ number → D.UInt.number number ≤ power 63 →
    I64.Integer.number (signedInteger number) ≡ Int.- (+ D.UInt.number number)
  signedIntegerExact number bounded = Magnitude.Width.negateWrapped 63 (D.UInt.number number) bounded

data Number : Set where
  unsigned64 : U64 → Number
  signed64 : I64.Integer → Number
  binary64 : A.Number → Number

data Reason : Set where invalidNumber eofValue numberOutOfRange arithmeticPanic : Reason
data Position : Set where current peek : Position
Code = Reason × Position
module C = Cursor.Over Char Code
Parsed = C.Result Number

