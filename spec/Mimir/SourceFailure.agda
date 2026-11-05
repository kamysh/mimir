{-# OPTIONS --safe #-}
-- Private judge source diagnostics, composed with the concrete JSON error
-- position/message and the checked lossy byte-to-text conversion.
module Mimir.SourceFailure where

open import Data.List using (List; length; _++_)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; _∸_; _*_; _≤_; zero; z≤n)
open import Data.Nat.Properties using (≤-trans; m∸n≤m; *-monoʳ-≤)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Bits using (Byte)
open import Mimir.Text using (Text; byteLength)
import Mimir.UnicodeText as Unicode
import Mimir.UTF8LossyText as Lossy
import Mimir.SourceWindow as Window
import Mimir.SourceLineOffset as Offset
import Mimir.JsonFlow as Flow
import Mimir.JsonErrorDisplay as Display
import Mimir.JsonDiagnosticCode as Diagnostic
import Mimir.JsonPosition as Position
module F = Flow.F

record Failure : Set where
  constructor failure
  field
    stage detail : Text
    totalBytes excerptStart : ℕ
    excerpt : Text

display : Failure → Text
display result = Failure.stage result ++ (toList ": " ++ Failure.detail result)

module Limits (width half : ℕ) where
  capture : Text → Text → List Byte → ℕ → Failure
  capture stage detail source start = failure stage detail (length source) start
    (Lossy.text (Window.bytes start width source))

  captureValid : ∀ stage detail source start → Unicode.Valid (Failure.excerpt (capture stage detail source start))
  captureValid stage detail source start = Lossy.valid (Window.bytes start width source)

  captureByteBound : ∀ stage detail source start → byteLength (Failure.excerpt (capture stage detail source start)) ≤ 3 * width
  captureByteBound stage detail source start = ≤-trans (Lossy.byteBound (Window.bytes start width source))
    (*-monoʳ-≤ 3 (Window.bounded start width source))

  input : Text → List Byte → Text → Failure
  input stage source detail = capture stage detail source 0

  inputValid : ∀ stage source detail → Unicode.Valid (Failure.excerpt (input stage source detail))
  inputValid stage source detail = captureValid stage detail source 0

  inputByteBound : ∀ stage source detail → byteLength (Failure.excerpt (input stage source detail)) ≤ 3 * width
  inputByteBound stage source detail = captureByteBound stage detail source 0

  position : ∀ {source} → F.Rejected source → Position.Position
  position rejection = Display.locate (proj₂ (F.Fault.code (F.Rejected.firstError rejection)))
    (F.Fault.origin (F.Rejected.firstError rejection))

  start : ∀ {source} → F.Rejected source → ℕ
  start {source} rejection = Offset.offset (Position.Position.line (position rejection))
    (Position.Position.column (position rejection)) source ∸ half

  startBound : ∀ {source} (rejection : F.Rejected source) → start rejection ≤ length source
  startBound {source} rejection = ≤-trans (m∸n≤m _ half)
    (Offset.offsetBound (Position.Position.line (position rejection))
      (Position.Position.column (position rejection)) source)

  windowEnd : ∀ {source} (rejection : F.Rejected source) →
    start rejection Data.Nat.+ length (Window.bytes (start rejection) width source) ≡
      Window.end (start rejection) width (length source)
  windowEnd {source} rejection = Window.endExact (start rejection) width source (startBound rejection)

  json : ∀ stage {source} (rejection : F.Rejected source) → Diagnostic.Rejection rejection → Failure
  json stage {source} rejection safe = capture stage (proj₁ (Diagnostic.renderAvailable rejection safe)) source (start rejection)

  exactDetail : ∀ stage {source} (rejection : F.Rejected source) safe →
    Display.renderRejected rejection ≡ just (Failure.detail (json stage rejection safe))
  exactDetail stage rejection safe = proj₂ (Diagnostic.renderAvailable rejection safe)

  exactSourceSize : ∀ stage {source} (rejection : F.Rejected source) safe →
    Failure.totalBytes (json stage rejection safe) ≡ length source
  exactSourceSize stage rejection safe = refl

  exactStage : ∀ stage {source} (rejection : F.Rejected source) safe →
    Failure.stage (json stage rejection safe) ≡ stage
  exactStage stage rejection safe = refl

  validExcerpt : ∀ stage {source} (rejection : F.Rejected source) safe →
    Unicode.Valid (Failure.excerpt (json stage rejection safe))
  validExcerpt stage {source} rejection safe = captureValid stage
    (proj₁ (Diagnostic.renderAvailable rejection safe)) source (start rejection)

  byteBound : ∀ stage {source} (rejection : F.Rejected source) safe →
    byteLength (Failure.excerpt (json stage rejection safe)) ≤ 3 * width
  byteBound stage {source} rejection safe = captureByteBound stage
    (proj₁ (Diagnostic.renderAvailable rejection safe)) source (start rejection)

  cleanupPreserves : ∀ stage {source} (rejection : F.Rejected source) safe after →
    json stage (F.extendRejected rejection after) (Diagnostic.extendRejection rejection after safe) ≡ json stage rejection safe
  cleanupPreserves stage (F.rejected faultValue oldCleanup) safe after = refl

-- The implementation constants limit the selected input to 32 KiB. The UTF-8
-- output may require up to 96 KiB, because one invalid byte becomes U+FFFD.
module Current = Limits (32 * 1024) (16 * 1024)
