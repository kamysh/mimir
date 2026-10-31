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
import Mimir.UTF8LossyText as Lossy
import Mimir.DiagnosticText as Bounded
import Mimir.McpClientLine as Line
import Mimir.UnicodeText as Unicode

subsequenceAll : ∀ {Predicate : Char → Set} {small large} →
  Bounded.Subsequence small large → All Predicate large → All Predicate small
subsequenceAll (Bounded.empty source) valid = All.[]
subsequenceAll (Bounded.keep character selected) (head All.∷ rest) = head All.∷ subsequenceAll selected rest
subsequenceAll (Bounded.skip character selected) (head All.∷ rest) = subsequenceAll selected rest

module With (limit : ℕ) where
  detail : List Byte → Text
  detail bytes = Bounded.bounded limit (Lossy.text bytes)

  appendDetail : Text → Text
  appendDetail [] = toList "MCP stream ended"
  appendDetail text@(_ ∷ _) = toList "MCP stream ended: " ++ text

  display : Line.Failure → Text
  display Line.deadlineExceeded = toList "MCP deadline exceeded"
  display Line.readTimeout = toList "MCP read timeout"
  display Line.tooLarge = toList "MCP response exceeds limit"
  display (Line.streamEnded bytes) = appendDetail (detail bytes)

  scalarBound : ∀ bytes → length (detail bytes) ≤ limit
  scalarBound bytes = Bounded.scalarBound limit (Lossy.text bytes)

  byteBound : ∀ bytes → byteLength (detail bytes) ≤ 4 * limit
  byteBound bytes = Bounded.byteBound limit (Lossy.text bytes)

  noControls : ∀ bytes → All Bounded.NonControl (detail bytes)
  noControls bytes = Bounded.boundedNonControl limit (Lossy.text bytes)

  preservesOrder : ∀ bytes → Bounded.Subsequence (detail bytes) (Lossy.text bytes)
  preservesOrder bytes = Bounded.preservesOrder limit (Lossy.text bytes)

  validDetail : ∀ bytes → Unicode.Valid (detail bytes)
  validDetail bytes = subsequenceAll (preservesOrder bytes) (Lossy.valid bytes)

  emptyDetail : ∀ bytes → detail bytes ≡ [] → display (Line.streamEnded bytes) ≡ toList "MCP stream ended"
  emptyDetail bytes empty rewrite empty = refl

  nonemptyDetail : ∀ bytes first rest → detail bytes ≡ first ∷ rest →
    display (Line.streamEnded bytes) ≡ toList "MCP stream ended: " ++ (first ∷ rest)
  nonemptyDetail bytes first rest exact rewrite exact = refl

module Current = With 512
