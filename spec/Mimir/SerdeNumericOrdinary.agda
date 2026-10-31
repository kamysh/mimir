{-# OPTIONS --safe #-}
-- With overflow checks disabled, every numeric-parser input has an ordinary
-- success/error outcome. Wrapping exponent arithmetic cannot become the
-- checked-profile panic branch. This does not assume a bound on input length.
import Mimir.FloatConversion
module Mimir.SerdeNumericOrdinary (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Char using (_≟_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (_+_; _*_; _≤?_)
import Data.Nat as Nat
open import Data.Integer using (+_)
import Data.Integer as Int
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Mimir.Binary64 using (positive; negative; powerMinusOne)
import Mimir.SerdeNumeric as NDependency
private
  module N = NDependency floatConversion
import Mimir.FloatConversion as Parts
import Mimir.DecimalLexer as Digits
import Mimir.Unsigned as D
import Mimir.SignedMachine as Machine
module P = N.Parser Machine.disabled

Ordinary : ∀ {Value input} → N.C.Result Value input → Set
Ordinary (N.C.success value before rest exact) = ⊤
Ordinary (N.C.failure (reason , position) before rest exact) = reason ≢ N.arithmeticPanic

prefix : ∀ {Value input} before (parsed : N.C.Result Value input) → Ordinary parsed → Ordinary (N.C.prefix before parsed)
prefix before (N.C.success value consumed remaining exact) ordinary = tt
prefix before (N.C.failure (reason , position) consumed remaining exact) ordinary = ordinary

finishParts : ∀ sign significand exponent input → Ordinary (N.finishParts sign significand exponent input)
finishParts sign significand exponent input with Parts.Contract.fromParts floatConversion sign (N.asFin significand) (N.I32.Integer.number exponent)
... | Parts.accepted number = tt
... | Parts.outOfRange = λ ()

finishInteger : ∀ sign significand input → Ordinary (N.finishInteger sign significand input)
finishInteger positive significand input = tt
finishInteger negative significand input with (+ 0) Int.≤? N.I64.Integer.number (N.signedInteger significand)
... | yes nonnegative = tt
... | no negativeInteger = tt

skipDigits : ∀ number input → Ordinary (N.skipDigits number input)
skipDigits number [] = tt
skipDigits number input@(c ∷ cs) with Digits.classify c
... | yes digit = prefix (c ∷ []) (N.skipDigits number cs) (skipDigits number cs)
... | no stopped = tt

exponentOverflow : ∀ sign significand exponentSign input → Ordinary (N.exponentOverflow sign significand exponentSign input)
exponentOverflow sign significand positive input with D.UInt.number significand Nat.≟ 0
... | yes zeroSignificand = skipDigits _ input
... | no nonzeroSignificand = λ ()
exponentOverflow sign significand negative input = skipDigits _ input

exponentDigits : ∀ sign significand starting exponentSign before input →
  Ordinary (N.exponentDigits sign significand starting exponentSign before input)
exponentDigits sign significand starting exponentSign before [] = finishParts sign significand (N.combineExponent starting exponentSign before) []
exponentDigits sign significand starting exponentSign before input@(c ∷ cs) with Digits.classify c
... | no stopped = finishParts sign significand (N.combineExponent starting exponentSign before) input
... | yes (digit , spelling) with (10 * D.UInt.number before + D.value digit) ≤? powerMinusOne 31
...   | no overflow = prefix (c ∷ []) (N.exponentOverflow sign significand exponentSign cs) (exponentOverflow sign significand exponentSign cs)
...   | yes fits = prefix (c ∷ []) (N.exponentDigits sign significand starting exponentSign (D.uint (10 * D.UInt.number before + D.value digit) fits) cs)
    (exponentDigits sign significand starting exponentSign (D.uint (10 * D.UInt.number before + D.value digit) fits) cs)

exponentFirst : ∀ sign significand starting exponentSign input → Ordinary (N.exponentFirst sign significand starting exponentSign input)
exponentFirst sign significand starting exponentSign [] = λ ()
exponentFirst sign significand starting exponentSign (c ∷ cs) with Digits.classify c
... | no invalid = λ ()
... | yes (digit , spelling) = prefix (c ∷ []) (N.exponentDigits sign significand starting exponentSign (N.digitExponent digit) cs)
  (exponentDigits sign significand starting exponentSign (N.digitExponent digit) cs)

exponentSign : ∀ sign significand starting input → Ordinary (N.exponentSign sign significand starting input)
exponentSign sign significand starting [] = λ ()
exponentSign sign significand starting input@(c ∷ cs) with c ≟ '+'
... | yes plus = prefix (c ∷ []) (N.exponentFirst sign significand starting positive cs) (exponentFirst sign significand starting positive cs)
... | no notPlus with c ≟ '-'
...   | yes minus = prefix (c ∷ []) (N.exponentFirst sign significand starting negative cs) (exponentFirst sign significand starting negative cs)
...   | no notMinus = exponentFirst sign significand starting positive input

withExponent : ∀ sign significand starting input → Ordinary (N.withExponent sign significand starting input)
withExponent sign significand starting [] = finishParts sign significand starting []
withExponent sign significand starting input@(c ∷ cs) with c ≟ 'e'
... | yes lower = prefix (c ∷ []) (N.exponentSign sign significand starting cs) (exponentSign sign significand starting cs)
... | no notLower with c ≟ 'E'
...   | yes upper = prefix (c ∷ []) (N.exponentSign sign significand starting cs) (exponentSign sign significand starting cs)
...   | no notUpper = finishParts sign significand starting input

skipFraction : ∀ sign significand exponent input → Ordinary (N.skipFraction sign significand exponent input)
skipFraction sign significand exponent [] = withExponent sign significand exponent []
skipFraction sign significand exponent input@(c ∷ cs) with Digits.classify c
... | yes digit = prefix (c ∷ []) (N.skipFraction sign significand exponent cs) (skipFraction sign significand exponent cs)
... | no stopped = withExponent sign significand exponent input

combinedFraction : ∀ sign significand before after input → Ordinary (P.combinedFraction sign significand before after input)
combinedFraction sign significand before after input = withExponent sign significand _ input

overflowingFraction : ∀ sign significand before after input → Ordinary (P.overflowingFraction sign significand before after input)
overflowingFraction sign significand before after input = skipFraction sign significand _ input

finishedFraction : ∀ sign significand before after input → Ordinary (P.finishedFraction sign significand before after input)
finishedFraction sign significand before after input with N.I32.Integer.number after Int.≟ (+ 0)
... | no nonzero = combinedFraction sign significand before after input
... | yes zero with input
...   | [] = λ ()
...   | c ∷ cs = λ ()

fractionDigits : ∀ sign significand before after input → Ordinary (P.fractionDigits sign significand before after input)
fractionDigits sign significand before after [] = finishedFraction sign significand before after []
fractionDigits sign significand before after input@(c ∷ cs) with Digits.classify c
... | no stopped = finishedFraction sign significand before after input
... | yes (digit , spelling) with (10 * D.UInt.number significand + D.value digit) ≤? powerMinusOne 64
...   | no overflow = overflowingFraction sign significand before after input
...   | yes fits = prefix (c ∷ []) (P.fractionDigits sign (D.uint (10 * D.UInt.number significand + D.value digit) fits) before
    (N.I32.wrap (N.I32.Integer.number after Int.- (+ 1))) cs)
    (fractionDigits sign (D.uint (10 * D.UInt.number significand + D.value digit) fits) before
      (N.I32.wrap (N.I32.Integer.number after Int.- (+ 1))) cs)

longInteger : ∀ sign significand exponent input → Ordinary (P.longInteger sign significand exponent input)
longInteger sign significand exponent [] = finishParts sign significand exponent []
longInteger sign significand exponent input@(c ∷ cs) with Digits.classify c
... | yes digit = prefix (c ∷ []) (P.longInteger sign significand (N.I32.wrap (N.I32.Integer.number exponent Int.+ (+ 1))) cs)
  (longInteger sign significand (N.I32.wrap (N.I32.Integer.number exponent Int.+ (+ 1))) cs)
... | no stopped with c ≟ '.'
...   | yes dot = prefix (c ∷ []) (P.fractionDigits sign significand exponent N.zeroCounter cs) (fractionDigits sign significand exponent N.zeroCounter cs)
...   | no notDot = withExponent sign significand exponent input

afterInteger : ∀ sign significand input → Ordinary (P.afterInteger sign significand input)
afterInteger sign significand [] = finishInteger sign significand []
afterInteger sign significand input@(c ∷ cs) with c ≟ '.'
... | yes dot = prefix (c ∷ []) (P.fractionDigits sign significand N.zeroCounter N.zeroCounter cs)
  (fractionDigits sign significand N.zeroCounter N.zeroCounter cs)
... | no notDot with c ≟ 'e'
...   | yes lower = prefix (c ∷ []) (N.exponentSign sign significand N.zeroCounter cs) (exponentSign sign significand N.zeroCounter cs)
...   | no notLower with c ≟ 'E'
...     | yes upper = prefix (c ∷ []) (N.exponentSign sign significand N.zeroCounter cs) (exponentSign sign significand N.zeroCounter cs)
...     | no notUpper = finishInteger sign significand input

integerDigits : ∀ sign significand input → Ordinary (P.integerDigits sign significand input)
integerDigits sign significand [] = afterInteger sign significand []
integerDigits sign significand input@(c ∷ cs) with Digits.classify c
... | no stopped = afterInteger sign significand input
... | yes (digit , spelling) with (10 * D.UInt.number significand + D.value digit) ≤? powerMinusOne 64
...   | no overflow = longInteger sign significand N.zeroCounter input
...   | yes fits = prefix (c ∷ []) (P.integerDigits sign (D.uint (10 * D.UInt.number significand + D.value digit) fits) cs)
    (integerDigits sign (D.uint (10 * D.UInt.number significand + D.value digit) fits) cs)

afterZero : ∀ sign input → Ordinary (P.afterZero sign input)
afterZero sign [] = afterInteger sign _ []
afterZero sign input@(c ∷ cs) with Digits.classify c
... | yes leadingZero = λ ()
... | no stopped = afterInteger sign _ input

integerFirst : ∀ sign input → Ordinary (P.integerFirst sign input)
integerFirst sign [] = λ ()
integerFirst sign (c ∷ cs) with c ≟ '0'
... | yes zero = prefix (c ∷ []) (P.afterZero sign cs) (afterZero sign cs)
... | no notZero with Digits.classify c
...   | no invalid = λ ()
...   | yes (digit , spelling) = prefix (c ∷ []) (P.integerDigits sign (N.digit64 digit) cs) (integerDigits sign (N.digit64 digit) cs)

read : ∀ input → Ordinary (P.read input)
read [] = λ ()
read input@(c ∷ cs) with c ≟ '-'
... | yes minus = prefix (c ∷ []) (P.integerFirst negative cs) (integerFirst negative cs)
... | no notMinus = integerFirst positive input
