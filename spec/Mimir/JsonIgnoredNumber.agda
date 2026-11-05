{-# OPTIONS --safe #-}
-- serde_json's ignored-number scanner. Digits are consumed syntactically:
-- no significand, exponent value, floating conversion or arithmetic overflow.
module Mimir.JsonIgnoredNumber where

open import Data.Char using (Char; _≟_)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.List.Properties using (++-identityʳ)
open import Data.Nat using (_≤_)
open import Data.Product using (_,_; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst)
import Mimir.DecimalLexer as Digits
import Mimir.Unsigned as Decimal
import Mimir.NumericTokens as Numeric
import Mimir.SequenceCursor as Cursor
import Mimir.ByteCursorTransport as Transport
import Mimir.ByteText as Wire
import Mimir.CursorProgress as Progress

module C = Cursor.Over Char Numeric.Code

digits : (∀ rest → C.Result ⊤ rest) → ∀ input → C.Result ⊤ input
digits next input with Digits.take input
... | Digits.run scanned rest exact stopped = C.reframe exact
  (C.prefix (map Decimal.character scanned) (next rest))

finish : ∀ input → C.Result ⊤ input
finish input = C.done tt input

exponentFirst : ∀ input → C.Result ⊤ input
exponentFirst [] = C.fail (Numeric.invalidNumber , Numeric.current) []
exponentFirst (char ∷ rest) with Digits.classify char
... | no invalid = C.prefix (char ∷ []) (C.fail (Numeric.invalidNumber , Numeric.current) rest)
... | yes digit = C.prefix (char ∷ []) (digits finish rest)

exponentSign : ∀ input → C.Result ⊤ input
exponentSign [] = exponentFirst []
exponentSign (char ∷ rest) with char ≟ '+'
... | yes refl = C.prefix ('+' ∷ []) (exponentFirst rest)
... | no notPlus with char ≟ '-'
...   | yes refl = C.prefix ('-' ∷ []) (exponentFirst rest)
...   | no notMinus = exponentFirst (char ∷ rest)

afterFraction : ∀ input → C.Result ⊤ input
afterFraction [] = finish []
afterFraction (char ∷ rest) with char ≟ 'e'
... | yes refl = C.prefix ('e' ∷ []) (exponentSign rest)
... | no notLower with char ≟ 'E'
...   | yes refl = C.prefix ('E' ∷ []) (exponentSign rest)
...   | no notUpper = finish (char ∷ rest)

fraction : ∀ input → C.Result ⊤ input
fraction input with Digits.take input
... | Digits.run [] rest exact stopped = C.fail (Numeric.invalidNumber , Numeric.peek) input
... | Digits.run (first ∷ scanned) rest exact stopped = C.reframe exact
  (C.prefix (Decimal.character first ∷ map Decimal.character scanned) (afterFraction rest))

afterInteger : ∀ input → C.Result ⊤ input
afterInteger [] = finish []
afterInteger (char ∷ rest) with char ≟ '.'
... | yes refl = C.prefix ('.' ∷ []) (fraction rest)
... | no notDot = afterFraction (char ∷ rest)

afterZero : ∀ input → C.Result ⊤ input
afterZero [] = afterInteger []
afterZero (char ∷ rest) with Digits.classify char
... | yes leadingZero = C.fail (Numeric.invalidNumber , Numeric.peek) (char ∷ rest)
... | no notDigit = afterInteger (char ∷ rest)

integer : ∀ input → C.Result ⊤ input
integer [] = C.fail (Numeric.invalidNumber , Numeric.current) []
integer (char ∷ rest) with char ≟ '0'
... | yes refl = C.prefix ('0' ∷ []) (afterZero rest)
... | no notZero with Digits.classify char
...   | no invalid = C.prefix (char ∷ []) (C.fail (Numeric.invalidNumber , Numeric.current) rest)
...   | yes nonzero = C.prefix (char ∷ []) (digits afterInteger rest)

read : ∀ input → C.Result ⊤ input
read [] = integer []
read (char ∷ rest) with char ≟ '-'
... | yes refl = C.prefix ('-' ∷ []) (integer rest)
... | no positive = integer (char ∷ rest)

module Bridge = Transport.Over Numeric.Code

readBytes : ∀ input → Bridge.B.Result ⊤ input
readBytes input = Bridge.transport (read (Wire.text input))

digitsConsumed : ∀ input → C.consumed (digits finish input) ≡
  map Decimal.character (Digits.Run.digits (Digits.take input))
digitsConsumed input with Digits.take input
... | Digits.run scanned rest refl stopped = ++-identityʳ (map Decimal.character scanned)

digitsRemaining : ∀ input → C.remaining (digits finish input) ≡ Digits.Run.suffix (Digits.take input)
digitsRemaining input with Digits.take input
... | Digits.run scanned rest refl stopped = refl

digitsSuffixComplete : ∀ scanned rest → Digits.Stopped rest →
  C.remaining (digits finish (map Decimal.character scanned ++ rest)) ≡ rest
digitsSuffixComplete scanned rest stopped =
  trans (digitsRemaining (map Decimal.character scanned ++ rest)) (proj₂ (Digits.complete scanned rest stopped))

module P = Progress.Over Char Numeric.Code

integerConsumes : ∀ char rest → 1 ≤ length (C.consumed (integer (char ∷ rest)))
integerConsumes char rest with char ≟ '0'
... | yes refl = P.prefixPositive '0' (afterZero rest)
... | no notZero with Digits.classify char
...   | no invalid = P.prefixPositive char (C.fail {Value = ⊤} (Numeric.invalidNumber , Numeric.current) rest)
...   | yes nonzero = P.prefixPositive char (digits afterInteger rest)

readConsumes : ∀ char rest → 1 ≤ length (C.consumed (read (char ∷ rest)))
readConsumes char rest with char ≟ '-'
... | yes refl = P.prefixPositive '-' (integer rest)
... | no positive = integerConsumes char rest

wireConsumes : ∀ byte rest → 1 ≤ length (Bridge.B.consumed (readBytes (byte ∷ rest)))
wireConsumes byte rest = subst (1 ≤_)
  (sym (Bridge.offsetPreserved {Value = ⊤} {input = byte ∷ rest} (read (Wire.text (byte ∷ rest)))))
  (readConsumes (Wire.character byte) (Wire.text rest))
