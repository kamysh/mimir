{-# OPTIONS --safe #-}
-- The source-failure search skips line-1 first-newline prefixes and then
-- clamps column-1. Missing lines select EOF, including empty input.
module Mimir.SourceLineOffset where

open import Data.List using (List; []; _++_; length)
open import Data.List.Properties using (length-++)
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _⊓_; z≤n)
open import Data.Nat.Properties using (+-monoʳ-≤; m⊓n≤n; +-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)
open import Mimir.Bits using (Byte)
import Data.Product
import Mimir.ReadLine as Line
import Mimir.SourceWindow as Window

skip : ℕ → List Byte → ℕ
skip zero source = 0
skip (suc count) source = length (Line.Scanned.bytes (Line.scan source)) +
  skip count (Line.Scanned.remainder (Line.scan source))

empty : ∀ count → skip count [] ≡ 0
empty zero = refl
empty (suc count) = empty count

bound : ∀ count source → skip count source ≤ length source
bound zero source = z≤n
bound (suc count) source = subst ((length prefix + skip count rest) ≤_) (sym exact)
  (+-monoʳ-≤ (length prefix) (bound count rest))
  where
  prefix = Line.Scanned.bytes (Line.scan source)
  rest = Line.Scanned.remainder (Line.scan source)
  exact : length source ≡ length prefix + length rest
  exact = trans (cong length (Line.scanConservesBytes source)) (length-++ prefix)

-- An independent execution relation uses the first-newline grammar rather
-- than the executable scanner. This also exposes the EOF behavior explicitly.
data Search : ℕ → List Byte → ℕ → Set where
  done : ∀ source → Search zero source 0
  step : ∀ count source prefix rest offset → Line.Split source prefix rest →
    Search count rest offset → Search (suc count) source (length prefix + offset)

meaning : ∀ count source → Search count source (skip count source)
meaning zero source = done source
meaning (suc count) source = step count source _ _ _
  (Line.Scanned.meaning (Line.scan source))
  (meaning count (Line.Scanned.remainder (Line.scan source)))

complete : ∀ {count source offset} → Search count source offset → skip count source ≡ offset
complete (done source) = refl
complete (step count source prefix rest offset split later)
  rewrite Data.Product.proj₁ (Line.scanComplete split) | Data.Product.proj₂ (Line.scanComplete split) =
    cong (length prefix +_) (complete later)

missingLine : ∀ count source → All Line.NotLF source → skip (suc count) source ≡ length source
missingLine count source ordinary = trans (complete (step count source source [] 0 split (emptySearch count)))
  (+-identityʳ (length source))
  where
  allBefore : ∀ bytes → All Line.NotLF bytes → Line.Split bytes bytes []
  allBefore [] All.[] = Line.atEOF
  allBefore (byte Data.List.∷ bytes) (ordinary All.∷ rest) =
    Line.beforeLF byte bytes bytes [] ordinary (allBefore bytes rest)
  split = allBefore source ordinary
  emptySearch : ∀ count → Search count [] 0
  emptySearch zero = done []
  emptySearch (suc count) = step count [] [] [] 0 Line.atEOF (emptySearch count)

offset : ℕ → ℕ → List Byte → ℕ
offset line column source = Window.clip (length source) (skip (line ∸ 1) source + (column ∸ 1))

offsetBound : ∀ line column source → offset line column source ≤ length source
offsetBound line column source = m⊓n≤n (skip (line ∸ 1) source + (column ∸ 1)) (length source)

nativeOffset : ∀ maximum line column source → length source ≤ maximum →
  ((skip (line ∸ 1) source + (column ∸ 1)) ⊓ maximum) ⊓ length source ≡ offset line column source
nativeOffset maximum line column source bounded = Window.saturatingClip maximum (length source)
  (skip (line ∸ 1) source + (column ∸ 1)) bounded
