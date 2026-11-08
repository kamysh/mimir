{-# OPTIONS --safe #-}
-- Complete joined stderr is displayed through the standard library's lossy
-- UTF-8 boundary. Original bytes and cleanup/read issues remain in the failure.
module Mimir.McpClientLineDiagnostic where

open import Data.List using (List; []; _∷_; _++_; concatMap)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Bits using (Byte)
open import Mimir.Text using (Text)
import Mimir.StandardLibrary as Library
import Mimir.McpClientLine as Line

module With (library : Library.Contract) where
  detail : List Byte → Text
  detail = Library.Contract.lossyUTF8 library

  appendDetail : Text → Text
  appendDetail [] = toList "MCP stream ended"
  appendDetail text@(_ ∷ _) = toList "MCP stream ended: " ++ text

  display : Line.Failure → Text
  display (Line.streamEnded captured) = appendDetail (detail (Line.Capture.bytes captured)) ++
    concatMap (λ issue → toList "; " ++ issue) (Line.Capture.issues captured)

  emptyDetail : ∀ bytes → detail bytes ≡ [] → display (Line.streamEnded (Line.capture bytes [])) ≡ toList "MCP stream ended"
  emptyDetail bytes empty rewrite empty = refl

  nonemptyDetail : ∀ bytes first rest → detail bytes ≡ first ∷ rest →
    display (Line.streamEnded (Line.capture bytes [])) ≡ (toList "MCP stream ended: " ++ (first ∷ rest)) ++ []
  nonemptyDetail bytes first rest exact rewrite exact = refl

module Current = With
