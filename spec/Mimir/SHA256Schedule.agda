{-# OPTIONS --safe #-}
-- The four-lane software message schedule agrees with the scalar sliding
-- window recurrence for every possible input block and word operations.
module Mimir.SHA256Schedule where

open import Data.Vec using (Vec; []; _∷_; _∷ʳ_; tail; map; zipWith)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Schedule (Word : Set) (add : Word → Word → Word) (sigma0 sigma1 : Word → Word) where
  Block = Vec Word 16
  Quad = Vec Word 4

  next : Block → Word
  next (w0 ∷ w1 ∷ w2 ∷ w3 ∷ w4 ∷ w5 ∷ w6 ∷ w7 ∷ w8 ∷ w9 ∷ w10 ∷ w11 ∷ w12 ∷ w13 ∷ w14 ∷ w15 ∷ []) =
    add (add (add w0 (sigma0 w1)) w9) (sigma1 w14)

  advance : Block → Block
  advance block = tail block ∷ʳ next block

  generate : ∀ count → Block → Vec Word count
  generate zero block = []
  generate (suc count) block = next block ∷ generate count (advance block)

  load : Quad → Quad → Quad
  load (a ∷ b ∷ c ∷ d ∷ []) (e ∷ f ∷ g ∷ h ∷ []) = h ∷ a ∷ b ∷ c ∷ []

  msg1 : Quad → Quad → Quad
  msg1 first second = zipWith add first (map sigma0 (load first second))

  msg2 : Quad → Quad → Quad
  msg2 (x3 ∷ x2 ∷ x1 ∷ x0 ∷ []) (w15 ∷ w14 ∷ ignored1 ∷ ignored2 ∷ []) =
    w19 ∷ w18 ∷ w17 ∷ w16 ∷ []
    where
    w16 = add x0 (sigma1 w14)
    w17 = add x1 (sigma1 w15)
    w18 = add x2 (sigma1 w16)
    w19 = add x3 (sigma1 w17)

  source : Quad → Quad → Quad → Quad → Quad
  source first second third fourth = msg2 (zipWith add (msg1 first second) (load third fourth)) fourth

  reverse4 : Quad → Quad
  reverse4 (a ∷ b ∷ c ∷ d ∷ []) = d ∷ c ∷ b ∷ a ∷ []

  first second third fourth : Block → Quad
  first  (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ j ∷ k ∷ l ∷ m ∷ n ∷ o ∷ p ∷ []) = d ∷ c ∷ b ∷ a ∷ []
  second (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ j ∷ k ∷ l ∷ m ∷ n ∷ o ∷ p ∷ []) = h ∷ g ∷ f ∷ e ∷ []
  third  (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ j ∷ k ∷ l ∷ m ∷ n ∷ o ∷ p ∷ []) = l ∷ k ∷ j ∷ i ∷ []
  fourth (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ j ∷ k ∷ l ∷ m ∷ n ∷ o ∷ p ∷ []) = p ∷ o ∷ n ∷ m ∷ []

  sourceEquivalent : ∀ block → source (first block) (second block) (third block) (fourth block) ≡ reverse4 (generate 4 block)
  sourceEquivalent (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ j ∷ k ∷ l ∷ m ∷ n ∷ o ∷ p ∷ []) = refl

  advanceFour : Block → Block
  advanceFour block = advance (advance (advance (advance block)))

  shiftFirst : ∀ block → first (advanceFour block) ≡ second block
  shiftFirst (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ j ∷ k ∷ l ∷ m ∷ n ∷ o ∷ p ∷ []) = refl

  shiftSecond : ∀ block → second (advanceFour block) ≡ third block
  shiftSecond (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ j ∷ k ∷ l ∷ m ∷ n ∷ o ∷ p ∷ []) = refl

  shiftThird : ∀ block → third (advanceFour block) ≡ fourth block
  shiftThird (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ j ∷ k ∷ l ∷ m ∷ n ∷ o ∷ p ∷ []) = refl

  shiftFourth : ∀ block → fourth (advanceFour block) ≡ source (first block) (second block) (third block) (fourth block)
  shiftFourth (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ j ∷ k ∷ l ∷ m ∷ n ∷ o ∷ p ∷ []) = refl
