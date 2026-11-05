{-# OPTIONS --safe #-}
-- All bounded unsigned judge fields round-trip through their raw byte reader.
import Mimir.FloatConversion
module Mimir.JudgeUnsignedReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Integer using (+_)
open import Data.List using (_++_)
open import Data.Nat using (_≤_)
open import Mimir.Binary64 using (powerMinusOne)
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

module Parser (checks : Machine.OverflowChecks) where
  roundTrip : ∀ maximum number → number ≤ maximum → number ≤ powerMinusOne 64 →
    ∀ suffix → Integer.Stopped (Wire.text suffix) →
    Back.Returns (Atoms.Parser.readUint checks maximum)
      (Encoding.spell (Writer.form (+ number)) ++ suffix) number suffix
  roundTrip maximum number within bounded suffix stopped = Number.Parser.checked checks (Atoms.uint maximum)
    Atoms.integerExpected
    (Encoding.spell (Writer.form (+ number)) ++ suffix)
    (Numeric.unsigned64 (D.uint number bounded)) suffix number
    (Start.append (Start.unsigned number) suffix)
    (Unsigned.Parser.roundTrip checks number bounded suffix stopped)
    (Primitive.uintRoundTrip maximum number within)
