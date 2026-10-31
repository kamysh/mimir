{-# OPTIONS --safe #-}
-- Negative canonical integers select signed conversion throughout i64 range.
import Mimir.FloatConversion
module Mimir.SerdeNegativeReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Char using (_≟_)
open import Data.List using ([]; _∷_; _++_; map)
open import Data.Nat using (suc; _≤_)
open import Data.Integer using (+_; -[1+_])
import Data.Integer as Int
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst)
open import Mimir.Binary64 using (negative; power; powerMinusOne)
import Mimir.Unsigned as D
import Mimir.DecimalLexer as Lexer
import Mimir.NatDecimal as Decimal
import Mimir.SerdeNumeric as NumericDependency
private
  module Numeric = NumericDependency floatConversion
import Mimir.SignedMachine as Machine
import Mimir.SerdeIntegerReadBack as IntegerDependency
private
  module Integer = IntegerDependency floatConversion
import Mimir.SerdeIntegerAccumulation as AccumulationDependency
private
  module Accumulation = AccumulationDependency floatConversion
private
  module B = Integer.B

notNonnegative : ∀ number → (+ 0) Int.≤ -[1+ number ] → ⊥
notNonnegative number ()

finish : ∀ number (bounded : suc number ≤ powerMinusOne 64) → suc number ≤ power 63 → ∀ suffix →
  B.Returned (Numeric.finishInteger negative (D.uint (suc number) bounded) suffix)
    (Numeric.signed64 (Numeric.signedInteger (D.uint (suc number) bounded))) suffix
finish number bounded signedBound suffix
  with (+ 0) Int.≤? Numeric.I64.Integer.number (Numeric.signedInteger (D.uint (suc number) bounded))
... | yes nonnegative = ⊥-elim
  (notNonnegative number
   (subst (+ 0 Int.≤_)
    (Numeric.signedIntegerExact (D.uint (suc number) bounded)
     signedBound)
    nonnegative))
... | no belowZero = B.returned

module Parser (checks : Machine.OverflowChecks) where
  private
    module N = Numeric.Parser checks
    module A = Accumulation.Parser checks

  first : ∀ digit tail final → digit ≢ D.d0 → D.Digits (D.value digit) tail final →
    (bounded : final ≤ powerMinusOne 64) → ∀ suffix → Integer.Stopped suffix → ∀ value →
    B.Returned (Numeric.finishInteger negative (D.uint final bounded) suffix) value suffix →
    B.Returned (N.integerFirst negative (D.character digit ∷ (tail ++ suffix))) value suffix
  first digit tail final nonzero interpretation bounded suffix stopped value finished with D.character digit ≟ '0'
  ... | yes zero = ⊥-elim (nonzero (D.zeroOnly digit zero))
  ... | no notZero rewrite Lexer.classifyComplete digit = B.prefix (D.character digit ∷ [])
    (A.accumulate negative (Numeric.digit64 digit) interpretation
     bounded suffix stopped value finished)

  magnitude : ∀ number (bounded : suc number ≤ powerMinusOne 64) → suc number ≤ power 63 →
    ∀ suffix → Integer.Stopped suffix →
    B.Returned (N.integerFirst negative (Decimal.text (suc number) ++ suffix))
      (Numeric.signed64 (Numeric.signedInteger (D.uint (suc number) bounded))) suffix
  magnitude number bounded signedBound suffix stopped = first (Decimal.Decimal.head (Decimal.encode (suc number)))
    (map D.character
     (Decimal.Decimal.tail (Decimal.encode (suc number))))
    (suc number)
    (Decimal.positiveHead number (Decimal.encode (suc number)))
    (subst
     (D.Digits
      (D.value (Decimal.Decimal.head (Decimal.encode (suc number))))
      (map D.character
       (Decimal.Decimal.tail (Decimal.encode (suc number)))))
     (Decimal.Decimal.exact (Decimal.encode (suc number)))
     (Decimal.interpretation
      (D.value (Decimal.Decimal.head (Decimal.encode (suc number))))
      (Decimal.Decimal.tail (Decimal.encode (suc number)))))
    bounded suffix stopped
    (Numeric.signed64
     (Numeric.signedInteger (D.uint (suc number) bounded)))
    (finish number bounded signedBound suffix)

  roundTrip : ∀ number (bounded : suc number ≤ powerMinusOne 64) → suc number ≤ power 63 →
    ∀ suffix → Integer.Stopped suffix →
    B.Returned (N.read ('-' ∷ (Decimal.text (suc number) ++ suffix)))
      (Numeric.signed64 (Numeric.signedInteger (D.uint (suc number) bounded))) suffix
  roundTrip number bounded signedBound suffix stopped = B.prefix ('-' ∷ [])
    (magnitude number bounded signedBound suffix stopped)
