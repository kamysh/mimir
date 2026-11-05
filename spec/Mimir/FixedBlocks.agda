{-# OPTIONS --safe #-}
-- Exact-size block partition with a strict remainder bound. All input is
-- retained, including an incomplete final block; no padding occurs here.
module Mimir.FixedBlocks where

open import Data.List using (List; []; _∷_; _++_; length)
import Data.List.Properties
open import Data.Vec as Vec using (Vec)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)

module Blocks (Atom : Set) where
  data Read (count : ℕ) (input : List Atom) : Set where
    full : ∀ (block : Vec Atom count) remaining → input ≡ Vec.toList block ++ remaining → Read count input
    short : length input < count → Read count input

  read : ∀ count input → Read count input
  read zero input = full Vec.[] input refl
  read (suc count) [] = short (s≤s z≤n)
  read (suc count) (entry ∷ rest) with read count rest
  ... | short bounded = short (s≤s bounded)
  ... | full block remaining exact = full (entry Vec.∷ block) remaining (cong (entry ∷_) exact)

  flatten : ∀ {count} → List (Vec Atom count) → List Atom
  flatten [] = []
  flatten (block ∷ rest) = Vec.toList block ++ flatten rest

  flattenAppend : ∀ {count} (first second : List (Vec Atom count)) → flatten (first ++ second) ≡ flatten first ++ flatten second
  flattenAppend [] second = refl
  flattenAppend (block ∷ rest) second = trans (cong (Vec.toList block ++_) (flattenAppend rest second))
    (sym (Data.List.Properties.++-assoc (Vec.toList block) (flatten rest) (flatten second)))

  record Partition (count : ℕ) (input : List Atom) : Set where
    constructor partition
    field
      blocks : List (Vec Atom count)
      remainder : List Atom
      exact : input ≡ flatten blocks ++ remainder
      shortRemainder : length remainder < count

  remainingBound : ∀ count (block : Vec Atom (suc count)) remaining input →
    input ≡ Vec.toList block ++ remaining → length remaining < length input
  remainingBound count (entry Vec.∷ block) remaining .(Vec.toList (entry Vec.∷ block) ++ remaining) refl =
    s≤s (Data.List.Properties.length-++-≤ʳ remaining {xs = Vec.toList block})

  bounded : ∀ count fuel input → length input < fuel → Partition (suc count) input
  bounded count zero input ()
  bounded count (suc fuel) input room with read (suc count) input
  ... | short small = partition [] input refl small
  ... | full block remaining exact with bounded count fuel remaining
    (Data.Nat.Properties.<-≤-trans (remainingBound count block remaining input exact) (Data.Nat.s≤s⁻¹ room))
  ...   | partition blocks rest tailExact small = partition (block ∷ blocks) rest
    (trans exact (trans (cong (Vec.toList block ++_) tailExact)
      (sym (Data.List.Properties.++-assoc (Vec.toList block) (flatten blocks) rest)))) small

  split : ∀ count input → Partition (suc count) input
  split count input = bounded count (suc (length input)) input (s≤s ≤-refl)
