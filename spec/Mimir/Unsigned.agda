{-# OPTIONS --safe #-}
-- The standard integer parser supplies success or failure. Mimir selects the
-- destination bound (for example 65535 for a port); it does not implement or
-- prove the parser digit loop, signs, overflow algorithm or error display.
module Mimir.Unsigned where

open import Data.Nat using (ℕ; _≤_)
open import Data.Sum using (_⊎_)
open import Mimir.Text using (Text)

record UInt (maximum : ℕ) : Set where
  constructor uint
  field number : ℕ; bounded : number ≤ maximum

data Error : Set where empty invalidDigit overflow : Error

record Parser : Set where
  field parse : (maximum : ℕ) → Text → Error ⊎ UInt maximum
open Parser public
