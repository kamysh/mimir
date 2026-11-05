{-# OPTIONS --safe #-}
-- Bounded digit accumulation stops before a nonnumeric suffix without overflow.
import Mimir.FloatConversion
module Mimir.SerdeIntegerReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Char using (Char; _≟_)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_; _++_)
open import Data.Nat using (_≤_; _≤?_; _+_; _*_)
open import Data.Nat.Properties using (≤-trans; ≤-irrelevant)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; subst)
open import Mimir.Binary64 using (positive; powerMinusOne)
open import Mimir.Text using (Text)
import Mimir.DecimalLexer as Lexer
import Mimir.Unsigned as D
import Mimir.SerdeNumeric as NumericDependency
private
  module Numeric = NumericDependency floatConversion
import Mimir.SignedMachine as Machine
import Mimir.SequenceReadBack as ReadBack

module B = ReadBack.Over Char Numeric.Code

Stopped : Text → Set
Stopped [] = ⊤
Stopped (c ∷ cs) = Lexer.NotDigit c × (c ≢ '.') × (c ≢ 'e') × (c ≢ 'E')

sameUInt : ∀ {maximum} (first second : D.UInt maximum) →
  D.UInt.number first ≡ D.UInt.number second → first ≡ second
sameUInt (D.uint number before) (D.uint .number after) refl = cong (D.uint number) (≤-irrelevant before after)

module Parser (checks : Machine.OverflowChecks) where
  private
    module N = Numeric.Parser checks

  afterStopped : ∀ number suffix → Stopped suffix →
    B.Returned (N.afterInteger positive number suffix) (Numeric.unsigned64 number) suffix
  afterStopped number [] stopped = B.returned
  afterStopped number (c ∷ suffix) (notDigit , notDot , notLower , notUpper) with c ≟ '.'
  ... | yes dot = ⊥-elim (notDot dot)
  ... | no _ with c ≟ 'e'
  ...   | yes lower = ⊥-elim (notLower lower)
  ...   | no _ with c ≟ 'E'
  ...     | yes upper = ⊥-elim (notUpper upper)
  ...     | no _ = B.returned

  digitsStopped : ∀ number suffix → Stopped suffix →
    B.Returned (N.integerDigits positive number suffix) (Numeric.unsigned64 number) suffix
  digitsStopped number [] stopped = B.returned
  digitsStopped number (c ∷ suffix) stopped@(notDigit , rest) with Lexer.classify c
  ... | yes (digit , spelling) = ⊥-elim (notDigit digit spelling)
  ... | no _ = afterStopped number (c ∷ suffix) stopped

  accumulate : ∀ {digits final} (before : Numeric.U64) →
    D.Digits (D.UInt.number before) digits final →
    (bounded : final ≤ powerMinusOne 64) → ∀ suffix → Stopped suffix →
    B.Returned (N.integerDigits positive before (digits ++ suffix))
      (Numeric.unsigned64 (D.uint final bounded)) suffix
  accumulate before (D.end n) bounded suffix stopped = B.retarget (digitsStopped before suffix stopped)
    (cong Numeric.unsigned64
     (sameUInt before (D.uint (D.UInt.number before) bounded) refl))
    refl
  accumulate before (D.next digit refl interpretation) bounded suffix stopped
    rewrite Lexer.classifyComplete digit
    with (10 * D.UInt.number before + D.value digit) ≤? powerMinusOne 64
  ... | no outside = ⊥-elim
    (outside (≤-trans (D.digitsMonotone interpretation) bounded))
  ... | yes fits = B.prefix (D.character digit ∷ [])
    (accumulate
     (D.uint (10 * D.UInt.number before + D.value digit) fits)
     interpretation bounded suffix stopped)
