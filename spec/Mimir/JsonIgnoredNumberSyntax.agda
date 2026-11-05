{-# OPTIONS --safe #-}
-- Complete JSON numeric spellings are accepted syntactically, at any digit length.
module Mimir.JsonIgnoredNumberSyntax where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym)
import Mimir.Unsigned as D
import Mimir.DecimalLexer as Digits
import Mimir.JsonIgnoredNumber as Reader
import Mimir.JsonIgnoredNumberReadBack as Back

data Sign : Set where absent plus minus : Sign
data Case : Set where lower upper : Case
data Integer : Set where
  zero : Integer
  nonzero : ∀ first → D.character first ≢ '0' → List D.Digit → Integer
data Fraction : Set where
  whole : Fraction
  fraction : D.Digit → List D.Digit → Fraction
data Exponent : Set where
  plain : Exponent
  exponent : Case → Sign → D.Digit → List D.Digit → Exponent

record Lexeme : Set where
  constructor lexeme
  field negative : Bool; integer : Integer; fractional : Fraction; exponential : Exponent

signBytes : Sign → List Char → List Char
signBytes absent input = input
signBytes plus input = '+' ∷ input
signBytes minus input = '-' ∷ input

marker : Case → Char
marker lower = 'e'
marker upper = 'E'

exponentBytes : Exponent → List Char → List Char
exponentBytes plain suffix = suffix
exponentBytes (exponent casing sign first rest) suffix =
  marker casing ∷ signBytes sign (D.character first ∷ (map D.character rest ++ suffix))

fractionBytes : Fraction → List Char → List Char
fractionBytes whole suffix = suffix
fractionBytes (fraction first rest) suffix = '.' ∷ D.character first ∷ (map D.character rest ++ suffix)

integerBytes : Integer → List Char → List Char
integerBytes zero suffix = '0' ∷ suffix
integerBytes (nonzero first valid rest) suffix = D.character first ∷ (map D.character rest ++ suffix)

spell : Lexeme → List Char → List Char
spell (lexeme false integer fractional exponential) suffix =
  integerBytes integer (fractionBytes fractional (exponentBytes exponential suffix))
spell (lexeme true integer fractional exponential) suffix =
  '-' ∷ integerBytes integer (fractionBytes fractional (exponentBytes exponential suffix))

Stable : (List Char → List Char) → Set
Stable encode = ∀ first second → encode (first ++ second) ≡ encode first ++ second

compose : ∀ first second → Stable first → Stable second → Stable (λ suffix → first (second suffix))
compose first second firstStable secondStable before after = trans (cong first (secondStable before after))
  (firstStable (second before) after)

signAppend : ∀ sign → Stable (signBytes sign)
signAppend absent first second = refl
signAppend plus first second = refl
signAppend minus first second = refl

exponentAppend : ∀ value → Stable (exponentBytes value)
exponentAppend plain first second = refl
exponentAppend (exponent casing sign digit rest) first second = cong (marker casing ∷_)
  (trans
   (cong (signBytes sign)
    (sym
     (++-assoc (D.character digit ∷ map D.character rest) first
      second)))
   (signAppend sign
    ((D.character digit ∷ map D.character rest) ++ first) second))

fractionAppend : ∀ value → Stable (fractionBytes value)
fractionAppend whole first second = refl
fractionAppend (fraction digit rest) first second = cong ('.' ∷_)
  (sym
   (++-assoc (D.character digit ∷ map D.character rest) first second))

integerAppend : ∀ value → Stable (integerBytes value)
integerAppend zero first second = refl
integerAppend (nonzero digit valid rest) first second = sym
  (++-assoc (D.character digit ∷ map D.character rest) first second)

unsignedAppend : ∀ integer fractional exponential →
  Stable (λ suffix → integerBytes integer (fractionBytes fractional (exponentBytes exponential suffix)))
unsignedAppend integer fractional exponential = compose (integerBytes integer)
  (λ suffix →
     fractionBytes fractional (exponentBytes exponential suffix))
  (integerAppend integer)
  (compose (fractionBytes fractional) (exponentBytes exponential)
   (fractionAppend fractional) (exponentAppend exponential))

spellAppend : ∀ value → Stable (spell value)
spellAppend (lexeme false integer fractional exponential) first second = unsignedAppend integer fractional exponential first second
spellAppend (lexeme true integer fractional exponential) first second = cong ('-' ∷_)
  (unsignedAppend integer fractional exponential first second)

signedExponent : ∀ sign first rest suffix → Digits.Stopped suffix →
  Back.Returned (Reader.exponentSign (signBytes sign (D.character first ∷ (map D.character rest ++ suffix)))) suffix
signedExponent absent first rest suffix stopped = Back.exponentUnsigned first (map D.character rest ++ suffix) suffix
  (Back.exponentFirst first rest suffix stopped)
signedExponent plus first rest suffix stopped = Back.exponentPlus
  (D.character first ∷ map D.character rest ++ suffix) suffix
  (Back.exponentFirst first rest suffix stopped)
signedExponent minus first rest suffix stopped = Back.exponentMinus
  (D.character first ∷ map D.character rest ++ suffix) suffix
  (Back.exponentFirst first rest suffix stopped)

afterFraction : ∀ exponential suffix → Back.Stopped suffix →
  Back.Returned (Reader.afterFraction (exponentBytes exponential suffix)) suffix
afterFraction plain suffix stopped = Back.afterFraction suffix stopped
afterFraction (exponent lower sign first rest) suffix stopped = Back.lowerExponent
  (signBytes sign
   (D.character first ∷ map D.character rest ++ suffix))
  suffix
  (signedExponent sign first rest suffix
   (Back.stoppedDigits suffix stopped))
afterFraction (exponent upper sign first rest) suffix stopped = Back.upperExponent
  (signBytes sign
   (D.character first ∷ map D.character rest ++ suffix))
  suffix
  (signedExponent sign first rest suffix
   (Back.stoppedDigits suffix stopped))

exponentStopped : ∀ exponential suffix → Back.Stopped suffix → Digits.Stopped (exponentBytes exponential suffix)
exponentStopped plain suffix stopped = Back.stoppedDigits suffix stopped
exponentStopped (exponent lower sign first rest) suffix stopped = Digits.notDecoded 'e' refl
exponentStopped (exponent upper sign first rest) suffix stopped = Digits.notDecoded 'E' refl

afterInteger : ∀ fractional exponential suffix → Back.Stopped suffix →
  Back.Returned (Reader.afterInteger (fractionBytes fractional (exponentBytes exponential suffix))) suffix
afterInteger whole plain suffix stopped = Back.afterInteger suffix stopped
afterInteger whole (exponent lower sign first rest) suffix stopped = Back.withoutFraction 'e'
  (signBytes sign
   (D.character first ∷ map D.character rest ++ suffix))
  suffix (λ ())
  (afterFraction (exponent lower sign first rest) suffix stopped)
afterInteger whole (exponent upper sign first rest) suffix stopped = Back.withoutFraction 'E'
  (signBytes sign
   (D.character first ∷ map D.character rest ++ suffix))
  suffix (λ ())
  (afterFraction (exponent upper sign first rest) suffix stopped)
afterInteger (fraction first rest) exponential suffix stopped = Back.withFraction
  (D.character first ∷
   map D.character rest ++ exponentBytes exponential suffix)
  suffix
  (Back.fraction first rest (exponentBytes exponential suffix) suffix
   (exponentStopped exponential suffix stopped)
   (afterFraction exponential suffix stopped))

fractionStopped : ∀ fractional exponential suffix → Back.Stopped suffix →
  Digits.Stopped (fractionBytes fractional (exponentBytes exponential suffix))
fractionStopped whole exponential suffix stopped = exponentStopped exponential suffix stopped
fractionStopped (fraction first rest) exponential suffix stopped = Digits.notDecoded '.' refl

integer : ∀ value fractional exponential suffix → Back.Stopped suffix →
  Back.Returned (Reader.integer (integerBytes value (fractionBytes fractional (exponentBytes exponential suffix)))) suffix
integer zero fractional exponential suffix stopped = Back.integerZero
  (fractionBytes fractional (exponentBytes exponential suffix))
  suffix (fractionStopped fractional exponential suffix stopped)
  (afterInteger fractional exponential suffix stopped)
integer (nonzero first valid rest) fractional exponential suffix stopped = Back.integerNonzero first rest
  (fractionBytes fractional (exponentBytes exponential suffix))
  suffix valid
  (fractionStopped fractional exponential suffix stopped)
  (afterInteger fractional exponential suffix stopped)

complete : ∀ value suffix → Back.Stopped suffix → Back.Returned (Reader.read (spell value suffix)) suffix
complete (lexeme false zero fractional exponential) suffix stopped = Back.positive D.d0
  (fractionBytes fractional (exponentBytes exponential suffix))
  suffix (integer zero fractional exponential suffix stopped)
complete (lexeme false (nonzero first valid rest) fractional exponential) suffix stopped = Back.positive first
  (map D.character rest ++
   fractionBytes fractional (exponentBytes exponential suffix))
  suffix
  (integer (nonzero first valid rest) fractional exponential suffix
   stopped)
complete (lexeme true value fractional exponential) suffix stopped = Back.negative
  (integerBytes value
   (fractionBytes fractional (exponentBytes exponential suffix)))
  suffix (integer value fractional exponential suffix stopped)
