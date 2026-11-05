{-# OPTIONS --safe #-}
-- Connect validated application inputs to standard numeric operations.
-- This is a carrier adapter, not an implementation of floating arithmetic.
module Mimir.ApplicationFloat where

open import Data.Float.Base using (Float; fromRatio; -_)
open import Data.Rational.Base using (ℚ; ↥_; ↧_)
open import Data.Maybe using (Maybe; just; nothing)
import Mimir.Binary64 as Binary

rational : ℚ → Float
rational q = fromRatio (↥ q) (↧ q)

signed : Binary.Sign → Float → Float
signed Binary.positive x = x
signed Binary.negative x = - x

finite : Binary.FiniteNumber → Float
finite n = signed (Binary.Word.sign (Binary.FiniteNumber.word n))
  (rational (Binary.unsignedValue (Binary.FiniteNumber.word n)))

number : Binary.Number → Maybe Float
number (Binary.finite n) = just (finite n)
number (Binary.nonfinite word proof) = nothing
