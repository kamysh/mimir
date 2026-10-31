{-# OPTIONS --safe #-}
-- Stable, lossless selection used by ordered output fields. The partition
-- carries both predicate evidence and an exact permutation of every entry.
module Mimir.StablePartition where

open import Data.Bool using (Bool; true; false; not; T)
open import Data.Unit using (tt)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as Perm
open import Relation.Binary.PropositionalEquality using (sym; subst; cong)

module For (Value : Set) (predicate : Value → Bool) where
  record Result (input : List Value) : Set where
    constructor partitioned
    field
      selected remainder : List Value
      exact : (selected ++ remainder) Perm.↭ input
      included : All (λ value → T (predicate value)) selected
      excluded : All (λ value → T (not (predicate value))) remainder

  partition : ∀ input → Result input
  partition [] = partitioned [] [] Perm.refl All.[] All.[]
  partition (value ∷ rest) with predicate value in observed | partition rest
  ... | true | partitioned selected remainder exact included excluded =
    partitioned (value ∷ selected) remainder (Perm.prep value exact)
      (subst T (sym observed) tt All.∷ included) excluded
  ... | false | partitioned selected remainder exact included excluded =
    partitioned selected (value ∷ remainder)
      (Perm.trans (Perm.shift value selected remainder) (Perm.prep value exact))
      included (subst (λ b → T (not b)) (sym observed) tt All.∷ excluded)
