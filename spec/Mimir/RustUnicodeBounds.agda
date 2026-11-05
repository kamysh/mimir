{-# OPTIONS --safe #-}
-- Every offset addition in either complete table fits Rust's u32 accumulator,
-- including an addition which causes the loop to stop at its next comparison.
module Mimir.RustUnicodeBounds where

open import Data.List.Relation.Unary.All using (All)
open import Data.List using (take; drop)
open import Data.Nat using (_<_; _<?_)
open import Data.Nat.ListAction using (sum)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Mimir.RustUnicodeData
open import Mimir.UnicodeSkipBounds using (updates; updatesBelow)

abstract
  alphabeticSumBound : sum alphabeticOffsets < 4294967296
  alphabeticSumBound = toWitness {a? = sum alphabeticOffsets <? 4294967296} tt

  numericSumBound : sum numericOffsets < 4294967296
  numericSumBound = toWitness {a? = sum numericOffsets <? 4294967296} tt

alphabeticUpdatesSafe : ∀ total count begin →
  All (_< 4294967296) (updates total 0 (take count (drop begin alphabeticOffsets)))
alphabeticUpdatesSafe total count begin = updatesBelow 4294967296 total count begin alphabeticOffsets alphabeticSumBound

numericUpdatesSafe : ∀ total count begin →
  All (_< 4294967296) (updates total 0 (take count (drop begin numericOffsets)))
numericUpdatesSafe total count begin = updatesBelow 4294967296 total count begin numericOffsets numericSumBound
