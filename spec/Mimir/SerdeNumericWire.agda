{-# OPTIONS --safe #-}
-- The streaming numeric model operating on original bytes.
import Mimir.FloatConversion
module Mimir.SerdeNumericWire (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.List using (List)
open import Mimir.Bits using (Byte)
import Mimir.ByteText as Wire
import Mimir.ByteCursorTransport as Transport
import Mimir.SerdeNumeric as NumericDependency
private
  module Numeric = NumericDependency floatConversion
import Mimir.SignedMachine as Machine

module Bridge = Transport.Over Numeric.Code

module Parser (checks : Machine.OverflowChecks) where
  module N = Numeric.Parser checks

  read : ∀ input → Bridge.B.Result Numeric.Number input
  read input = Bridge.transport (N.read (Wire.text input))
