{-# OPTIONS --safe #-}
-- Transport both successful and failed byte/character parsers, preserving
-- values, errors, consumed offsets and unconsumed bytes.
module Mimir.ByteCursorTransport where

open import Data.Char using (Char)
open import Data.List using (List; _++_; length)
open import Data.List.Properties using (map-++; length-map)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.All.Properties using (++⁻ˡ; ++⁻ʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym; subst)
open import Mimir.Bits using (Byte)
import Mimir.ByteText as Wire
import Mimir.SequenceCursor as Cursor

module Over (Code : Set) where
  module T = Cursor.Over Char Code
  module B = Cursor.Over Byte Code

  record Split (input : List Byte) (consumed remaining : List Char) : Set where
    constructor split
    field
      prefix suffix : List Byte
      prefixText : Wire.text prefix ≡ consumed
      suffixText : Wire.text suffix ≡ remaining
      exact : input ≡ prefix ++ suffix

  splitAt : ∀ input consumed remaining → Wire.text input ≡ consumed ++ remaining → Split input consumed remaining
  splitAt input consumed remaining reconstruct = split prefix suffix prefixText suffixText
    (Wire.textInjective input (prefix ++ suffix) (trans reconstruct
      (sym (trans (map-++ Wire.character prefix suffix) (cong₂ _++_ prefixText suffixText)))))
    where
    bounds = subst (All Wire.Bounded) reconstruct (Wire.textBounded input)
    prefix = Wire.bytes consumed (++⁻ˡ consumed bounds)
    suffix = Wire.bytes remaining (++⁻ʳ consumed bounds)
    prefixText = Wire.textBytes consumed (++⁻ˡ consumed bounds)
    suffixText = Wire.textBytes remaining (++⁻ʳ consumed bounds)

  transport : ∀ {Value input} → T.Result Value (Wire.text input) → B.Result Value input
  transport {input = input} (T.success value consumed remaining exact) with splitAt input consumed remaining exact
  ... | split prefix suffix prefixText suffixText equation = B.success value prefix suffix equation
  transport {input = input} (T.failure code consumed remaining exact) with splitAt input consumed remaining exact
  ... | split prefix suffix prefixText suffixText equation = B.failure code prefix suffix equation

  consumedText : ∀ {Value input} (result : T.Result Value (Wire.text input)) →
    Wire.text (B.consumed (transport result)) ≡ T.consumed result
  consumedText {input = input} (T.success value consumed remaining exact) = Split.prefixText (splitAt input consumed remaining exact)
  consumedText {input = input} (T.failure code consumed remaining exact) = Split.prefixText (splitAt input consumed remaining exact)

  remainingText : ∀ {Value input} (result : T.Result Value (Wire.text input)) →
    Wire.text (B.remaining (transport result)) ≡ T.remaining result
  remainingText {input = input} (T.success value consumed remaining exact) = Split.suffixText (splitAt input consumed remaining exact)
  remainingText {input = input} (T.failure code consumed remaining exact) = Split.suffixText (splitAt input consumed remaining exact)

  offsetPreserved : ∀ {Value input} (result : T.Result Value (Wire.text input)) →
    length (B.consumed (transport result)) ≡ length (T.consumed result)
  offsetPreserved result = trans (sym (length-map Wire.character (B.consumed (transport result)))) (cong length (consumedText result))
