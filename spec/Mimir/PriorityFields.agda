{-# OPTIONS --safe #-}
-- Priority groups preserve every key/value entry exactly. Selection is stable
-- within a key; sorted input objects have at most one entry for each key.
module Mimir.PriorityFields where

open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Nullary using (does)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as Perm
import Mimir.ByteKeyOrder as Key
import Mimir.OrderedObject as Objects
import Mimir.StablePartition as Partition

module For (Value : Set) where
  Field = Key.Key × Value
  Fields = List Field

  matches : Key.Key → Field → Bool
  matches name entry = does (name Objects.≟Key proj₁ entry)

  module P (name : Key.Key) = Partition.For Field (matches name)

  record Selected (input : Fields) : Set where
    constructor selected
    field chosen remainder : Fields; exact : (chosen ++ remainder) Perm.↭ input

  select : List Key.Key → ∀ input → Selected input
  select [] input = selected [] input Perm.refl
  select (name ∷ names) input with P.partition name input
  ... | P.partitioned chosen remainder exact included excluded with select names remainder
  ...   | selected next rest nextExact = selected (chosen ++ next) rest
      (Perm.trans (Perm.++-assoc chosen next rest)
        (Perm.trans (Perm.++⁺ˡ chosen nextExact) exact))

  record Reordered (input : Fields) : Set where
    constructor reordered
    field fields : Fields; exact : fields Perm.↭ input

  reorder : List Key.Key → List Key.Key → ∀ input → Reordered input
  reorder first last input with select first input
  ... | selected front rest frontExact with select last rest
  ...   | selected back middle backExact = reordered (front ++ (middle ++ back))
      (Perm.trans (Perm.++⁺ˡ front (Perm.trans (Perm.++-comm middle back) backExact)) frontExact)
