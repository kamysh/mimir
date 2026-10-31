{-# OPTIONS --safe #-}
-- Digit accumulation preserves an established final conversion for either sign.
import Mimir.FloatConversion
module Mimir.SerdeIntegerAccumulation (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Char using (_≟_)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_; _++_)
open import Data.Nat using (_≤_; _≤?_; _+_; _*_)
open import Data.Nat.Properties using (≤-trans)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (refl; sym; subst)
open import Mimir.Binary64 using (powerMinusOne)
import Mimir.DecimalLexer as Lexer
import Mimir.Unsigned as D
import Mimir.SerdeNumeric as NumericDependency
private
  module Numeric = NumericDependency floatConversion
import Mimir.SignedMachine as Machine
import Mimir.SerdeIntegerReadBack as IntegerDependency
private
  module Integer = IntegerDependency floatConversion
private
  module B = Integer.B

module Parser (checks : Machine.OverflowChecks) where
  private
    module N = Numeric.Parser checks

  afterStopped : ∀ sign number suffix → Integer.Stopped suffix → ∀ value →
    B.Returned (Numeric.finishInteger sign number suffix) value suffix →
    B.Returned (N.afterInteger sign number suffix) value suffix
  afterStopped sign number [] stopped value finished = finished
  afterStopped sign number (c ∷ suffix) (notDigit , notDot , notLower , notUpper) value finished with c ≟ '.'
  ... | yes dot = ⊥-elim (notDot dot)
  ... | no _ with c ≟ 'e'
  ...   | yes lower = ⊥-elim (notLower lower)
  ...   | no _ with c ≟ 'E'
  ...     | yes upper = ⊥-elim (notUpper upper)
  ...     | no _ = finished

  digitsStopped : ∀ sign number suffix → Integer.Stopped suffix → ∀ value →
    B.Returned (Numeric.finishInteger sign number suffix) value suffix →
    B.Returned (N.integerDigits sign number suffix) value suffix
  digitsStopped sign number [] stopped value finished = finished
  digitsStopped sign number (c ∷ suffix) stopped@(notDigit , rest) value finished with Lexer.classify c
  ... | yes (digit , spelling) = ⊥-elim (notDigit digit spelling)
  ... | no _ = afterStopped sign number (c ∷ suffix) stopped value finished

  accumulate : ∀ sign {digits final} (before : Numeric.U64) →
    D.Digits (D.UInt.number before) digits final →
    (bounded : final ≤ powerMinusOne 64) → ∀ suffix → Integer.Stopped suffix → ∀ value →
    B.Returned (Numeric.finishInteger sign (D.uint final bounded) suffix) value suffix →
    B.Returned (N.integerDigits sign before (digits ++ suffix)) value suffix
  accumulate sign before (D.end n) bounded suffix stopped value finished = digitsStopped sign before suffix stopped value
    (subst
     (λ n →
        B.Returned (Numeric.finishInteger sign n suffix) value suffix)
     (sym
      (Integer.sameUInt before (D.uint (D.UInt.number before) bounded)
       refl))
     finished)
  accumulate sign before (D.next digit refl interpretation) bounded suffix stopped value finished
    rewrite Lexer.classifyComplete digit
    with (10 * D.UInt.number before + D.value digit) ≤? powerMinusOne 64
  ... | no outside = ⊥-elim
    (outside (≤-trans (D.digitsMonotone interpretation) bounded))
  ... | yes fits = B.prefix (D.character digit ∷ [])
    (accumulate sign
     (D.uint (10 * D.UInt.number before + D.value digit) fits)
     interpretation bounded suffix stopped value finished)
