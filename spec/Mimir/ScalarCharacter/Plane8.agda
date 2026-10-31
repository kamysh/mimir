{-# OPTIONS --safe #-}
-- Exhaustive kernel-checked conversion fact for Unicode plane 8.
module Mimir.ScalarCharacter.Plane8 where
open import Data.Bool using (T)
open import Data.Unit using (tt)
open import Mimir.ScalarCharacterCheck using (module C)
abstract
  checked : T (C.all 16 524288)
  checked = tt
