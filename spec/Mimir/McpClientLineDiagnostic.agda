{-# OPTIONS --safe #-}
-- Existing client read diagnostics: lossy stderr decoding, control removal,
-- and the 512-scalar limit precede the empty-detail decision.
module Mimir.McpClientLineDiagnostic where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
open import Data.Char using (Char)
open import Data.Nat using (ℕ; _≤_; _*_)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Bits using (Byte)
open import Mimir.Text using (Text; byteLength)
import Mimir.StandardLibrary as Library
import Mimir.DiagnosticText as Bounded
import Mimir.McpClientLine as Line

module With (limit : ℕ) (library : Library.Contract) where
  detail : List Byte → Text
  detail bytes = Bounded.bounded limit (Library.Contract.lossyUTF8 library bytes)

  appendDetail : Text → Text
  appendDetail [] = toList "MCP stream ended"
  appendDetail text@(_ ∷ _) = toList "MCP stream ended: " ++ text

  display : Line.Failure → Text
  display (Line.streamEnded bytes) = appendDetail (detail bytes)

  scalarBound : ∀ bytes → length (detail bytes) ≤ limit
  scalarBound bytes = Bounded.scalarBound limit (Library.Contract.lossyUTF8 library bytes)

  byteBound : ∀ bytes → byteLength (detail bytes) ≤ 4 * limit
  byteBound bytes = Bounded.byteBound limit (Library.Contract.lossyUTF8 library bytes)

  noControls : ∀ bytes → All Bounded.NonControl (detail bytes)
  noControls bytes = Bounded.boundedNonControl limit (Library.Contract.lossyUTF8 library bytes)

  preservesOrder : ∀ bytes → Bounded.Subsequence (detail bytes) (Library.Contract.lossyUTF8 library bytes)
  preservesOrder bytes = Bounded.preservesOrder limit (Library.Contract.lossyUTF8 library bytes)

  emptyDetail : ∀ bytes → detail bytes ≡ [] → display (Line.streamEnded bytes) ≡ toList "MCP stream ended"
  emptyDetail bytes empty rewrite empty = refl

  nonemptyDetail : ∀ bytes first rest → detail bytes ≡ first ∷ rest →
    display (Line.streamEnded bytes) ≡ toList "MCP stream ended: " ++ (first ∷ rest)
  nonemptyDetail bytes first rest exact rewrite exact = refl

module Current = With 512
