{-# OPTIONS --safe #-}
-- Every representable i64 judge field round-trips through its raw byte reader.
import Mimir.FloatConversion
module Mimir.JudgeSignedReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Integer using (+_; -[1+_])
open import Data.Nat using (suc)
open import Data.List using (_++_)
open import Relation.Binary.PropositionalEquality using (cong; trans)
import Mimir.ByteText as Wire
import Mimir.JsonNumberWire as Encoding
import Mimir.JsonIntegerWriter as Writer
import Mimir.JudgeStateAtoms as AtomsDependency
private
  module Atoms = AtomsDependency floatConversion
import Mimir.JudgeStatePrimitives as Primitive
import Mimir.SerdeUnsignedWireReadBack as UnsignedDependency
private
  module Unsigned = UnsignedDependency floatConversion
import Mimir.SerdeNegativeWireReadBack as NegativeDependency
private
  module Negative = NegativeDependency floatConversion
import Mimir.SerdeNumberReadBack as NumberDependency
private
  module Number = NumberDependency floatConversion
import Mimir.SerdeNumberStart as StartDependency
private
  module Start = StartDependency floatConversion
import Mimir.SerdeIntegerReadBack as IntegerDependency
private
  module Integer = IntegerDependency floatConversion
import Mimir.SerdeReadBack as Back
import Mimir.NumericTokens as Numeric
import Mimir.Unsigned as D
import Mimir.SignedMachine as Machine
import Mimir.SignedIntegerBounds as Bounds

module Parser (checks : Machine.OverflowChecks) where
  roundTrip : ∀ number → Primitive.I64.InRange number →
    ∀ suffix → Integer.Stopped (Wire.text suffix) →
    Back.Returns (Atoms.Parser.readSigned checks)
      (Encoding.spell (Writer.form number) ++ suffix) number suffix
  roundTrip (+ number) within suffix stopped = Number.Parser.checked checks Atoms.signed Atoms.integerExpected
    (Encoding.spell (Writer.form (+ number)) ++ suffix)
    (Numeric.unsigned64
     (D.uint number (Bounds.Width.positiveUnsigned 63 number within)))
    suffix (+ number) (Start.append (Start.unsigned number) suffix)
    (Unsigned.Parser.roundTrip checks number
     (Bounds.Width.positiveUnsigned 63 number within) suffix stopped)
    (Primitive.signedNumberRoundTrip (+ number) within)
  roundTrip -[1+ number ] within suffix stopped = Number.Parser.checked checks Atoms.signed Atoms.integerExpected
    (Encoding.spell (Writer.form -[1+ number ]) ++ suffix)
    (Numeric.signed64
     (Numeric.signedInteger
      (D.uint (suc number)
       (Bounds.Width.negativeUnsigned 63 number within))))
    suffix -[1+ number ] (Start.append (Negative.starts number) suffix)
    (Negative.Parser.roundTrip checks number
     (Bounds.Width.negativeUnsigned 63 number within)
     (Bounds.Width.negative 63 number within) suffix stopped)
    (trans
     (cong Primitive.signedNumber
      (Numeric.signedIntegerExact
       (D.uint (suc number)
        (Bounds.Width.negativeUnsigned 63 number within))
       (Bounds.Width.negative 63 number within)))
     (Primitive.signedNumberRoundTrip -[1+ number ] within))
