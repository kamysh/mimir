{-# OPTIONS --safe #-}
-- Negative canonical JSON bytes preserve the signed result and their suffix.
import Mimir.FloatConversion
module Mimir.SerdeNegativeWireReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Integer using (-[1+_])
open import Data.List using (_∷_; _++_)
open import Data.List.Properties using (map-++)
open import Data.Nat using (suc; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import Mimir.Binary64 using (power; powerMinusOne)
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
import Mimir.SerdeNegativeReadBack as NegativeDependency
private
  module Negative = NegativeDependency floatConversion
import Mimir.SerdeNumberStart as StartDependency
private
  module Start = StartDependency floatConversion
import Mimir.SignedMachine as Machine

spelling : ∀ number suffix →
  Wire.text (Encoding.spell (Writer.form -[1+ number ]) ++ suffix) ≡
    '-' ∷ (Decimal.text (suc number) ++ Wire.text suffix)
spelling number suffix = trans
  (map-++ Wire.character (Encoding.spell (Writer.form -[1+ number ]))
   suffix)
  (cong (_++ Wire.text suffix)
   (trans (Encoding.Prefix.spellingText (Writer.form -[1+ number ]))
    (Writer.spelling -[1+ number ])))

starts : ∀ number → Start.Starts (Encoding.spell (Writer.form -[1+ number ]))
starts number = Start.starts _ _ refl refl

module Parser (checks : Machine.OverflowChecks) where
  private
    module B = Back.Over Byte Numeric.Code
    module N = Numeric.Parser checks

  roundTrip : ∀ number (bounded : suc number ≤ powerMinusOne 64) → suc number ≤ power 63 →
    ∀ suffix → Integer.Stopped (Wire.text suffix) →
    B.Returned (Reader.Parser.read checks (Encoding.spell (Writer.form -[1+ number ]) ++ suffix))
      (Numeric.signed64 (Numeric.signedInteger (D.uint (suc number) bounded))) suffix
  roundTrip number bounded signedBound suffix stopped = Transport.Over.transport Numeric.Code
    (subst
     (λ input →
        Integer.B.Returned (N.read input)
        (Numeric.signed64
         (Numeric.signedInteger (D.uint (suc number) bounded)))
        (Wire.text suffix))
     (sym (spelling number suffix))
     (Negative.Parser.roundTrip checks number bounded signedBound
      (Wire.text suffix) stopped))
