{-# OPTIONS --safe #-}
-- The reversible byte bridge preserves successful values and exact suffixes.
module Mimir.ByteReadBack where

open import Data.Char using (Char)
open import Relation.Binary.PropositionalEquality using (refl)
open import Mimir.Bits using (Byte)
import Mimir.ByteText as Wire
import Mimir.ByteCursorTransport as Transport
import Mimir.SequenceReadBack as ReadBack

module Over (Code : Set) where
  private
    module Bridge = Transport.Over Code
    module T = ReadBack.Over Char Code
    module B = ReadBack.Over Byte Code

  transport : ∀ {Value input} {result : Bridge.T.Result Value (Wire.text input)} {value suffix} →
    T.Returned result value (Wire.text suffix) → B.Returned (Bridge.transport result) value suffix
  transport {input = input} {result = Bridge.T.success value consumed rest exact} {suffix = suffix} T.returned =
    B.retarget B.returned refl (Wire.bytesText suffix _)
