{-# OPTIONS --safe #-}
-- Exact fixed-width partitioning. Both directions are inverse for every
-- element type, chunk width and number of chunks.
module Mimir.VectorChunks where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Vec using (Vec; []; _∷_; _++_; splitAt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)

size : ℕ → ℕ → ℕ
size width zero = 0
size width (suc count) = width + size width count

flatten : ∀ {A : Set} {width count} → Vec (Vec A width) count → Vec A (size width count)
flatten [] = []
flatten (chunk ∷ rest) = chunk ++ flatten rest

chunks : ∀ {A : Set} width count → Vec A (size width count) → Vec (Vec A width) count
chunks width zero [] = []
chunks width (suc count) input with splitAt width input
... | first , rest , exact = first ∷ chunks width count rest

flattenChunks : ∀ {A : Set} width count (input : Vec A (size width count)) → flatten (chunks width count input) ≡ input
flattenChunks width zero [] = refl
flattenChunks width (suc count) input with splitAt width input
... | first , rest , exact = trans (cong (first ++_) (flattenChunks width count rest)) (sym exact)

splitAppend : ∀ {A : Set} {width tailSize} (first : Vec A width) (rest : Vec A tailSize) →
  splitAt width (first ++ rest) ≡ (first , rest , refl)
splitAppend [] rest = refl
splitAppend (entry ∷ first) rest rewrite splitAppend first rest = refl

chunksFlatten : ∀ {A : Set} {width count} (input : Vec (Vec A width) count) → chunks width count (flatten input) ≡ input
chunksFlatten [] = refl
chunksFlatten {width = width} (first ∷ rest) rewrite splitAppend first (flatten rest) =
  cong (first ∷_) (chunksFlatten rest)
