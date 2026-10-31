{-# OPTIONS --safe #-}
-- Canonical unsigned decimal encodings round-trip through number conversion.
import Mimir.FloatConversion
module Mimir.SerdeUnsignedReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Char using (_≟_)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_; _++_; map)
open import Data.Nat using (_≤_; z≤n)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import Mimir.Binary64 using (positive; powerMinusOne)
import Mimir.DecimalLexer as Lexer
import Mimir.Unsigned as D
import Mimir.NatDecimal as Decimal
import Mimir.SerdeNumeric as NumericDependency
private
  module Numeric = NumericDependency floatConversion
import Mimir.SignedMachine as Machine
import Mimir.SerdeIntegerReadBack as IntegerDependency
private
  module Integer = IntegerDependency floatConversion

module Parser (checks : Machine.OverflowChecks) where
  private
    module N = Numeric.Parser checks
    module I = Integer.Parser checks
    module B = Integer.B

  zeroStopped : ∀ suffix → Integer.Stopped suffix →
    B.Returned (N.afterZero positive suffix) (Numeric.unsigned64 (D.uint 0 z≤n)) suffix
  zeroStopped [] stopped = B.returned
  zeroStopped (c ∷ suffix) stopped@(notDigit , rest) with Lexer.classify c
  ... | yes (digit , spelling) = ⊥-elim (notDigit digit spelling)
  ... | no _ = I.afterStopped (D.uint 0 z≤n) (c ∷ suffix) stopped

  first : ∀ digit tail final → D.Digits (D.value digit) tail final →
    (digit ≡ D.d0 → tail ≡ []) → (bounded : final ≤ powerMinusOne 64) →
    ∀ suffix → Integer.Stopped suffix →
    B.Returned (N.integerFirst positive (D.character digit ∷ (tail ++ suffix)))
      (Numeric.unsigned64 (D.uint final bounded)) suffix
  first digit tail final interpretation leading bounded suffix stopped with D.character digit ≟ '0'
  ... | yes zero with D.zeroOnly digit zero
  ...   | refl with leading refl
  ...     | refl with interpretation
  ...       | D.end .0 = B.retarget (B.prefix ('0' ∷ []) (zeroStopped suffix stopped))
    (cong Numeric.unsigned64
     (Integer.sameUInt (D.uint 0 z≤n) (D.uint 0 bounded) refl))
    refl
  first digit tail final interpretation leading bounded suffix stopped | no nonzero
    rewrite Lexer.classifyComplete digit = B.prefix (D.character digit ∷ [])
      (I.accumulate (Numeric.digit64 digit) interpretation bounded suffix
       stopped)

  readDigits : ∀ digit tail final → D.Digits (D.value digit) tail final →
    (digit ≡ D.d0 → tail ≡ []) → (bounded : final ≤ powerMinusOne 64) →
    ∀ suffix → Integer.Stopped suffix →
    B.Returned (N.read (D.character digit ∷ (tail ++ suffix)))
      (Numeric.unsigned64 (D.uint final bounded)) suffix
  readDigits digit tail final interpretation leading bounded suffix stopped with D.character digit ≟ '-'
  ... | yes minus = ⊥-elim (D.digitNotMinus digit minus)
  ... | no _ = first digit tail final interpretation leading bounded suffix
    stopped

  representation : ∀ number (decimal : Decimal.Decimal number)
    (bounded : number ≤ powerMinusOne 64) suffix → Integer.Stopped suffix →
    B.Returned (N.read (map D.character (Decimal.digits decimal) ++ suffix))
      (Numeric.unsigned64 (D.uint number bounded)) suffix
  representation number (Decimal.decimal head tail refl leadingZero) bounded suffix stopped = readDigits head (map D.character tail)
    (Decimal.fold (D.value head) tail)
    (Decimal.interpretation (D.value head) tail)
    (λ same → cong (map D.character) (leadingZero same)) bounded suffix
    stopped

  roundTrip : ∀ number (bounded : number ≤ powerMinusOne 64) suffix → Integer.Stopped suffix →
    B.Returned (N.read (Decimal.text number ++ suffix))
      (Numeric.unsigned64 (D.uint number bounded)) suffix
  roundTrip number bounded suffix stopped = representation number (Decimal.encode number) bounded suffix
    stopped
