{-# OPTIONS --safe #-}
-- Canonical unsigned JSON bytes retain their value and the following bytes.
import Mimir.FloatConversion
module Mimir.SerdeUnsignedWireReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Integer using (+_)
open import Data.List using (_++_)
open import Data.List.Properties using (map-++)
open import Data.Nat using (_≤_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; trans; sym; subst)
open import Mimir.Binary64 using (powerMinusOne)
open import Mimir.Bits using (Byte)
import Mimir.ByteText as Wire
import Mimir.ByteReadBack as Transport
import Mimir.SequenceReadBack as Back
import Mimir.JsonNumberWire as Encoding
import Mimir.JsonIntegerWriter as Writer
import Mimir.NatDecimal as Decimal
import Mimir.Unsigned as D
import Mimir.SerdeNumeric as NumericDependency
private
  module Numeric = NumericDependency floatConversion
import Mimir.SerdeNumericWire as ReaderDependency
private
  module Reader = ReaderDependency floatConversion
import Mimir.SerdeIntegerReadBack as IntegerDependency
private
  module Integer = IntegerDependency floatConversion
import Mimir.SerdeUnsignedReadBack as UnsignedDependency
private
  module Unsigned = UnsignedDependency floatConversion
import Mimir.SignedMachine as Machine

spelling : ∀ number suffix →
  Wire.text (Encoding.spell (Writer.form (+ number)) ++ suffix) ≡ Decimal.text number ++ Wire.text suffix
spelling number suffix = trans
  (map-++ Wire.character (Encoding.spell (Writer.form (+ number)))
   suffix)
  (cong (_++ Wire.text suffix)
   (trans (Encoding.Prefix.spellingText (Writer.form (+ number)))
    (Writer.spelling (+ number))))

module Parser (checks : Machine.OverflowChecks) where
  private
    module B = Back.Over Byte Numeric.Code
    module N = Numeric.Parser checks

  roundTrip : ∀ number (bounded : number ≤ powerMinusOne 64) suffix → Integer.Stopped (Wire.text suffix) →
    B.Returned (Reader.Parser.read checks (Encoding.spell (Writer.form (+ number)) ++ suffix))
      (Numeric.unsigned64 (D.uint number bounded)) suffix
  roundTrip number bounded suffix stopped = Transport.Over.transport Numeric.Code
    (subst
     (λ input →
        Integer.B.Returned (N.read input)
        (Numeric.unsigned64 (D.uint number bounded)) (Wire.text suffix))
     (sym (spelling number suffix))
     (Unsigned.Parser.roundTrip checks number bounded (Wire.text suffix)
      stopped))
