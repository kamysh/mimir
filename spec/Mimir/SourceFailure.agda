{-# OPTIONS --safe #-}
-- Mimir's private diagnostic window. JSON positions/messages and replacement
-- text decoding come from the supplied standard-library boundary.
module Mimir.SourceFailure where

open import Data.List using (List; length; _++_)
open import Data.Nat using (ℕ; _∸_; _*_; _≤_)
open import Data.Nat.Properties using (≤-trans; m∸n≤m; *-monoʳ-≤)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Bits using (Byte)
open import Mimir.Text using (Text; byteLength)
import Mimir.StandardLibrary as Library
import Mimir.SourceWindow as Window
import Mimir.SourceLineOffset as Offset

record Failure : Set where
  constructor failure
  field
    stage detail : Text
    totalBytes excerptStart : ℕ
    excerpt : Text

display : Failure → Text
display result = Failure.stage result ++ (toList ": " ++ Failure.detail result)

module Limits (width half : ℕ) (library : Library.Contract) where
  capture : Text → Text → List Byte → ℕ → Failure
  capture stage detail source start = failure stage detail (length source) start
    (Library.Contract.lossyUTF8 library (Window.bytes start width source))

  captureByteBound : ∀ stage detail source start →
    byteLength (Failure.excerpt (capture stage detail source start)) ≤ 3 * width
  captureByteBound stage detail source start = ≤-trans
    (Library.Contract.lossyByteBound library (Window.bytes start width source))
    (*-monoʳ-≤ 3 (Window.bounded start width source))

  input : Text → List Byte → Text → Failure
  input stage source detail = capture stage detail source 0

  inputByteBound : ∀ stage source detail → byteLength (Failure.excerpt (input stage source detail)) ≤ 3 * width
  inputByteBound stage source detail = captureByteBound stage detail source 0

  start : List Byte → Library.JSONError → ℕ
  start source error = Offset.offset (Library.JSONError.line error) (Library.JSONError.column error) source ∸ half

  startBound : ∀ source error → start source error ≤ length source
  startBound source error = ≤-trans (m∸n≤m _ half)
    (Offset.offsetBound (Library.JSONError.line error) (Library.JSONError.column error) source)

  windowEnd : ∀ source error →
    start source error Data.Nat.+ length (Window.bytes (start source error) width source) ≡
      Window.end (start source error) width (length source)
  windowEnd source error = Window.endExact (start source error) width source (startBound source error)

  json : Text → List Byte → Library.JSONError → Failure
  json stage source error = capture stage (Library.JSONError.message error) source (start source error)

  exactDetail : ∀ stage source error → Failure.detail (json stage source error) ≡ Library.JSONError.message error
  exactDetail stage source error = refl

  exactSourceSize : ∀ stage source error → Failure.totalBytes (json stage source error) ≡ length source
  exactSourceSize stage source error = refl

  exactStage : ∀ stage source error → Failure.stage (json stage source error) ≡ stage
  exactStage stage source error = refl

  byteBound : ∀ stage source error → byteLength (Failure.excerpt (json stage source error)) ≤ 3 * width
  byteBound stage source error = captureByteBound stage (Library.JSONError.message error) source (start source error)

module Current = Limits (32 * 1024) (16 * 1024)
