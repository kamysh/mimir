{-# OPTIONS --safe #-}
-- Exhaustive kernel-checked conversion fact for Unicode plane 15.
module Mimir.ScalarCharacter.Plane15 where
open import Data.Bool using (T)
open import Data.Unit using (tt)
open import Mimir.ScalarCharacterCheck using (module C)
abstract
  checked : T (C.all 16 983040)
  checked = tt
