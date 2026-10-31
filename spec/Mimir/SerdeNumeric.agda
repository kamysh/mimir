{-# OPTIONS --safe #-}
-- Streaming default serde_json number conversion. Input is the reversible
-- byte/character representation, so ASCII predicates do not decode Unicode.
-- Fatal checked-arithmetic overflow is distinct from a JSON parse failure.
import Mimir.FloatConversion
module Mimir.SerdeNumeric (floatConversion : Mimir.FloatConversion.Contract) where

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
import Mimir.FloatConversion as Parts
import Mimir.SequenceCursor as Cursor

open import Mimir.NumericTokens public

finishParts : Sign → U64 → I32.Integer → ∀ input → Parsed input
finishParts sign significand exponent input with Parts.Contract.fromParts floatConversion sign (asFin significand) (I32.Integer.number exponent)
... | Parts.accepted number = C.done (binary64 number) input
... | Parts.outOfRange = C.fail (numberOutOfRange , current) input

finishInteger : Sign → U64 → ∀ input → Parsed input
finishInteger positive significand input = C.done (unsigned64 significand) input
finishInteger negative significand input with (+ 0) Int.≤? I64.Integer.number (signedInteger significand)
... | yes nonnegative = C.done (binary64 (A.negate (Parts.Contract.cast floatConversion (asFin significand)))) input
... | no isNegative = C.done (signed64 (signedInteger significand)) input

skipDigits : Number → ∀ input → Parsed input
skipDigits number [] = C.done number []
skipDigits number input@(c ∷ cs) with Digits.classify c
... | yes digit = C.prefix (c ∷ []) (skipDigits number cs)
... | no stopped = C.done number input

exponentOverflow : Sign → U64 → Sign → ∀ input → Parsed input
exponentOverflow sign significand positive input with D.UInt.number significand Nat.≟ 0
... | yes zeroSignificand = skipDigits (binary64 (A.signedZero sign)) input
... | no nonzeroSignificand = C.fail (numberOutOfRange , current) input
exponentOverflow sign significand negative input = skipDigits (binary64 (A.signedZero sign)) input

combineExponent : I32.Integer → Sign → Exponent → I32.Integer
combineExponent starting positive exponent = I32.saturatingAdd starting (+ D.UInt.number exponent)
combineExponent starting negative exponent = I32.saturatingSubtract starting (+ D.UInt.number exponent)

exponentDigits : Sign → U64 → I32.Integer → Sign → Exponent → ∀ input → Parsed input
exponentDigits sign significand starting exponentSign before [] =
  finishParts sign significand (combineExponent starting exponentSign before) []
exponentDigits sign significand starting exponentSign before input@(c ∷ cs) with Digits.classify c
... | no stopped = finishParts sign significand (combineExponent starting exponentSign before) input
... | yes (digit , spelling) with (10 * D.UInt.number before + D.value digit) ≤? powerMinusOne 31
...   | no overflow = C.prefix (c ∷ []) (exponentOverflow sign significand exponentSign cs)
...   | yes fits = C.prefix (c ∷ []) (exponentDigits sign significand starting exponentSign
      (D.uint (10 * D.UInt.number before + D.value digit) fits) cs)

exponentFirst : Sign → U64 → I32.Integer → Sign → ∀ input → Parsed input
exponentFirst sign significand starting exponentSign [] = C.fail (eofValue , current) []
exponentFirst sign significand starting exponentSign (c ∷ cs) with Digits.classify c
... | no invalid = C.prefix (c ∷ []) (C.fail (invalidNumber , current) cs)
... | yes (digit , spelling) = C.prefix (c ∷ [])
    (exponentDigits sign significand starting exponentSign (digitExponent digit) cs)

exponentSign : Sign → U64 → I32.Integer → ∀ input → Parsed input
exponentSign sign significand starting [] = exponentFirst sign significand starting positive []
exponentSign sign significand starting input@(c ∷ cs) with c ≟ '+'
... | yes plus = C.prefix (c ∷ []) (exponentFirst sign significand starting positive cs)
... | no notPlus with c ≟ '-'
...   | yes minus = C.prefix (c ∷ []) (exponentFirst sign significand starting negative cs)
...   | no notMinus = exponentFirst sign significand starting positive input

withExponent : Sign → U64 → I32.Integer → ∀ input → Parsed input
withExponent sign significand starting [] = finishParts sign significand starting []
withExponent sign significand starting input@(c ∷ cs) with c ≟ 'e'
... | yes lower = C.prefix (c ∷ []) (exponentSign sign significand starting cs)
... | no notLower with c ≟ 'E'
...   | yes upper = C.prefix (c ∷ []) (exponentSign sign significand starting cs)
...   | no notUpper = finishParts sign significand starting input

skipFraction : Sign → U64 → I32.Integer → ∀ input → Parsed input
skipFraction sign significand exponent [] = withExponent sign significand exponent []
skipFraction sign significand exponent input@(c ∷ cs) with Digits.classify c
... | yes digit = C.prefix (c ∷ []) (skipFraction sign significand exponent cs)
... | no stopped = withExponent sign significand exponent input

module Parser (checks : Machine.OverflowChecks) where
  combinedFraction : Sign → U64 → I32.Integer → I32.Integer → ∀ input → Parsed input
  combinedFraction sign significand before after input with I32.execute checks (I32.Integer.number before Int.+ I32.Integer.number after)
  ... | I32.panic outside = C.fail (arithmeticPanic , current) input
  ... | I32.returned exponent = withExponent sign significand exponent input

  overflowingFraction : Sign → U64 → I32.Integer → I32.Integer → ∀ input → Parsed input
  overflowingFraction sign significand before after input with I32.execute checks (I32.Integer.number before Int.+ I32.Integer.number after)
  ... | I32.panic outside = C.fail (arithmeticPanic , current) input
  ... | I32.returned exponent = skipFraction sign significand exponent input

  finishedFraction : Sign → U64 → I32.Integer → I32.Integer → ∀ input → Parsed input
  finishedFraction sign significand before after input with I32.Integer.number after Int.≟ (+ 0)
  ... | no nonzero = combinedFraction sign significand before after input
  ... | yes zero with input
  ...   | [] = C.fail (eofValue , peek) []
  ...   | c ∷ cs = C.fail (invalidNumber , peek) (c ∷ cs)

  fractionDigits : Sign → U64 → I32.Integer → I32.Integer → ∀ input → Parsed input
  fractionDigits sign significand before after [] = finishedFraction sign significand before after []
  fractionDigits sign significand before after input@(c ∷ cs) with Digits.classify c
  ... | no stopped = finishedFraction sign significand before after input
  ... | yes (digit , spelling) with (10 * D.UInt.number significand + D.value digit) ≤? powerMinusOne 64
  ...   | no overflow = overflowingFraction sign significand before after input
  ...   | yes fits with I32.execute checks (I32.Integer.number after Int.- (+ 1))
  ...     | I32.panic outside = C.prefix (c ∷ []) (C.fail (arithmeticPanic , current) cs)
  ...     | I32.returned next = C.prefix (c ∷ []) (fractionDigits sign
        (D.uint (10 * D.UInt.number significand + D.value digit) fits) before next cs)

  longInteger : Sign → U64 → I32.Integer → ∀ input → Parsed input
  longInteger sign significand exponent [] = finishParts sign significand exponent []
  longInteger sign significand exponent input@(c ∷ cs) with Digits.classify c
  ... | yes digit with I32.execute checks (I32.Integer.number exponent Int.+ (+ 1))
  ...   | I32.panic outside = C.prefix (c ∷ []) (C.fail (arithmeticPanic , current) cs)
  ...   | I32.returned next = C.prefix (c ∷ []) (longInteger sign significand next cs)
  longInteger sign significand exponent input@(c ∷ cs) | no stopped with c ≟ '.'
  ... | yes dot = C.prefix (c ∷ []) (fractionDigits sign significand exponent zeroCounter cs)
  ... | no notDot = withExponent sign significand exponent input

  afterInteger : Sign → U64 → ∀ input → Parsed input
  afterInteger sign significand [] = finishInteger sign significand []
  afterInteger sign significand input@(c ∷ cs) with c ≟ '.'
  ... | yes dot = C.prefix (c ∷ []) (fractionDigits sign significand zeroCounter zeroCounter cs)
  ... | no notDot with c ≟ 'e'
  ...   | yes lower = C.prefix (c ∷ []) (exponentSign sign significand zeroCounter cs)
  ...   | no notLower with c ≟ 'E'
  ...     | yes upper = C.prefix (c ∷ []) (exponentSign sign significand zeroCounter cs)
  ...     | no notUpper = finishInteger sign significand input

  integerDigits : Sign → U64 → ∀ input → Parsed input
  integerDigits sign significand [] = afterInteger sign significand []
  integerDigits sign significand input@(c ∷ cs) with Digits.classify c
  ... | no stopped = afterInteger sign significand input
  ... | yes (digit , spelling) with (10 * D.UInt.number significand + D.value digit) ≤? powerMinusOne 64
  ...   | no overflow = longInteger sign significand zeroCounter input
  ...   | yes fits = C.prefix (c ∷ []) (integerDigits sign (D.uint (10 * D.UInt.number significand + D.value digit) fits) cs)

  afterZero : Sign → ∀ input → Parsed input
  afterZero sign [] = afterInteger sign (D.uint 0 z≤n) []
  afterZero sign input@(c ∷ cs) with Digits.classify c
  ... | yes leadingZero = C.fail (invalidNumber , peek) input
  ... | no stopped = afterInteger sign (D.uint 0 z≤n) input

  integerFirst : Sign → ∀ input → Parsed input
  integerFirst sign [] = C.fail (eofValue , current) []
  integerFirst sign (c ∷ cs) with c ≟ '0'
  ... | yes zero = C.prefix (c ∷ []) (afterZero sign cs)
  ... | no notZero with Digits.classify c
  ...   | no invalid = C.prefix (c ∷ []) (C.fail (invalidNumber , current) cs)
  ...   | yes (digit , spelling) = C.prefix (c ∷ []) (integerDigits sign (digit64 digit) cs)

  read : ∀ input → Parsed input
  read [] = integerFirst positive []
  read input@(c ∷ cs) with c ≟ '-'
  ... | yes minus = C.prefix (c ∷ []) (integerFirst negative cs)
  ... | no notMinus = integerFirst positive input
