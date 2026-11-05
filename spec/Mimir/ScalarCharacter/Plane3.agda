{-# OPTIONS --safe #-}
-- Exhaustive kernel-checked conversion fact for Unicode plane 3.
module Mimir.ScalarCharacter.Plane3 where
open import Data.Bool using (T)
open import Data.Unit using (tt)
open import Mimir.ScalarCharacterCheck using (module C)
abstract
  checked : T (C.all 16 196608)
  checked = tt
