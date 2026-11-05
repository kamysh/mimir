{-# OPTIONS --safe #-}
-- External numeric-conversion interface. Consumers quantify over it; this
-- module supplies no instance and introduces no postulate. Native serde/Rust
-- correspondence is an explicit open obligation, not a proved implementation.
module Mimir.FloatConversion where

open import Data.Fin using (Fin)
open import Data.Integer using (ℤ)
open import Mimir.Binary64 using (Sign; power)
import Mimir.FloatValue as Float

data Result : Set where
  accepted : Float.Number → Result
  outOfRange : Result

record Contract : Set where
  field
    cast : Fin (power 64) → Float.Number
    fromParts : Sign → Fin (power 64) → ℤ → Result
