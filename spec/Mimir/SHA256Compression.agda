{-# OPTIONS --safe #-}
-- Batching four optimized rounds preserves the complete scalar round fold,
-- for arbitrary round-group counts, states and message/constant addends.
module Mimir.SHA256Compression where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Vec using (Vec; []; _∷_; _++_)
open import Data.List as List using (List)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
import Mimir.SHA256Round as Round

module Compression (Word : Set) (add : Word → Word → Word)
  (associative : ∀ a b c → add (add a b) c ≡ add a (add b c))
  (commutative : ∀ a b → add a b ≡ add b a)
  (bigSigma0 bigSigma1 : Word → Word)
  (choose majority : Word → Word → Word → Word) where
  module R = Round.Rounds Word add associative commutative bigSigma0 bigSigma1 choose majority
  open R using (State; state)

  run : ∀ {count} → Vec Word count → State → State
  run [] initial = initial
  run (wk ∷ rest) initial = run rest (R.standard wk initial)

  runAppend : ∀ {firstCount secondCount} (first : Vec Word firstCount) (second : Vec Word secondCount) initial →
    run (first ++ second) initial ≡ run second (run first initial)
  runAppend [] second initial = refl
  runAppend (wk ∷ rest) second initial = runAppend rest second (R.standard wk initial)

  groupWidth : ℕ → ℕ
  groupWidth zero = 0
  groupWidth (suc count) = 4 + groupWidth count

  grouped : ∀ count → Vec Word (groupWidth count) → State → State
  grouped zero [] initial = initial
  grouped (suc count) (wk0 ∷ wk1 ∷ wk2 ∷ wk3 ∷ rest) initial =
    grouped count rest (R.four initial wk0 wk1 wk2 wk3)

  groupedEquivalent : ∀ count (words : Vec Word (groupWidth count)) initial → grouped count words initial ≡ run words initial
  groupedEquivalent zero [] initial = refl
  groupedEquivalent (suc count) (wk0 ∷ wk1 ∷ wk2 ∷ wk3 ∷ rest) initial =
    trans (groupedEquivalent count rest (R.four initial wk0 wk1 wk2 wk3))
      (cong (run rest) (R.fourStandard initial wk0 wk1 wk2 wk3))

  feedForward : State → State → State
  feedForward (state a b c d e f g h) (state a′ b′ c′ d′ e′ f′ g′ h′) =
    state (add a a′) (add b b′) (add c c′) (add d d′) (add e e′) (add f f′) (add g g′) (add h h′)

  compress compressGrouped : Vec Word 64 → State → State
  compress words initial = feedForward initial (run words initial)
  compressGrouped words initial = feedForward initial (grouped 16 words initial)

  compressionEquivalent : ∀ words initial → compressGrouped words initial ≡ compress words initial
  compressionEquivalent words initial = cong (feedForward initial) (groupedEquivalent 16 words initial)

  many : List (Vec Word 64) → State → State
  many List.[] initial = initial
  many (words List.∷ rest) initial = many rest (compress words initial)

  manyAppend : ∀ first second initial → many (first List.++ second) initial ≡ many second (many first initial)
  manyAppend List.[] second initial = refl
  manyAppend (words List.∷ rest) second initial = manyAppend rest second (compress words initial)
