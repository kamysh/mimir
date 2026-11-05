{-# OPTIONS --safe #-}
-- Exhaustive kernel-checked conversion fact for Unicode plane 16.
module Mimir.ScalarCharacter.Plane16 where
open import Data.Bool using (T)
open import Data.Unit using (tt)
open import Mimir.ScalarCharacterCheck using (module C)
abstract
  checked : T (C.all 16 1048576)
  checked = tt
