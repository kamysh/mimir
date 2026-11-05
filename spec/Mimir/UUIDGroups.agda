{-# OPTIONS --safe #-}
-- All 128-bit UUID values, grouped exactly as the 8-4-4-4-12 wire layout.
-- This type includes nil/non-v4 values accepted by the stored-data reader.
module Mimir.UUIDGroups where

open import Data.Vec using (Vec; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Bits using (Byte)

UUID = Vec Byte 16

record Groups : Set where
  constructor groups
  field first : Vec Byte 4; second third fourth : Vec Byte 2; fifth : Vec Byte 6

flatten : Groups → UUID
flatten (groups first second third fourth fifth) = first ++ (second ++ (third ++ (fourth ++ fifth)))

split : UUID → Groups
split (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ j ∷ k ∷ l ∷ m ∷ n ∷ o ∷ p ∷ []) =
  groups (a ∷ b ∷ c ∷ d ∷ []) (e ∷ f ∷ []) (g ∷ h ∷ []) (i ∷ j ∷ []) (k ∷ l ∷ m ∷ n ∷ o ∷ p ∷ [])

flattenSplit : ∀ value → flatten (split value) ≡ value
flattenSplit (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ j ∷ k ∷ l ∷ m ∷ n ∷ o ∷ p ∷ []) = refl

splitFlatten : ∀ value → split (flatten value) ≡ value
splitFlatten (groups (a ∷ b ∷ c ∷ d ∷ []) (e ∷ f ∷ []) (g ∷ h ∷ []) (i ∷ j ∷ []) (k ∷ l ∷ m ∷ n ∷ o ∷ p ∷ [])) = refl
