{-# OPTIONS --safe #-}
-- A numeric parser invoked on nonempty input consumes a byte even on failure.
-- This gives the recursive JSON decoder a proved decreasing input measure.
import Mimir.FloatConversion
module Mimir.SerdeNumericProgress (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Char using (Char; _≟_)
open import Data.List using (_∷_; []; length)
open import Data.Nat using (_≤_)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (sym; subst)
open import Mimir.Binary64 using (Sign; positive; negative)
import Mimir.DecimalLexer as Digits
import Mimir.SerdeNumeric as NumericDependency
private
  module Numeric = NumericDependency floatConversion
import Mimir.SerdeNumericWire as WireParserDependency
private
  module WireParser = WireParserDependency floatConversion
import Mimir.ByteText as Wire
import Mimir.SignedMachine as Machine
import Mimir.CursorProgress as Progress

module Parser (checks : Machine.OverflowChecks) where
  module N = Numeric.Parser checks
  module P = Progress.Over Char Numeric.Code
  module W = WireParser.Parser checks

  integerFirstConsumes : ∀ sign c cs → 1 ≤ length (Numeric.C.consumed (N.integerFirst sign (c ∷ cs)))
  integerFirstConsumes sign c cs with c ≟ '0'
  ... | yes zero = P.prefixPositive c (N.afterZero sign cs)
  ... | no notZero with Digits.classify c
  ...   | no invalid = P.prefixPositive c (Numeric.C.fail {Value = Numeric.Number} (Numeric.invalidNumber , Numeric.current) cs)
  ...   | yes (digit , spelling) = P.prefixPositive c (N.integerDigits sign (Numeric.digit64 digit) cs)

  readConsumes : ∀ c cs → 1 ≤ length (Numeric.C.consumed (N.read (c ∷ cs)))
  readConsumes c cs with c ≟ '-'
  ... | yes minus = P.prefixPositive c (N.integerFirst negative cs)
  ... | no notMinus = integerFirstConsumes positive c cs

  wireConsumes : ∀ byte rest → 1 ≤ length (WireParser.Bridge.B.consumed (W.read (byte ∷ rest)))
  wireConsumes byte rest = subst (1 ≤_)
    (sym (WireParser.Bridge.offsetPreserved {Value = Numeric.Number} {input = byte ∷ rest} (N.read (Wire.text (byte ∷ rest)))))
    (readConsumes (Wire.character byte) (Wire.text rest))
