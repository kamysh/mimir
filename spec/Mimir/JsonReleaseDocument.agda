{-# OPTIONS --safe #-}
-- Concrete complete JSON decoding for the release overflow profile. The
-- outcome carries exact source bytes and either a complete schema parsedDocument
-- or its original syntax diagnostic; no arbitrary decoder is supplied.
import Mimir.FloatConversion
module Mimir.JsonReleaseDocument (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.List using (List; [])
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Mimir.Bits using (Byte)
open import Mimir.Text using (Text)
import Mimir.JsonOrdinary as OrdinaryDependency
private
  module Ordinary = OrdinaryDependency floatConversion
import Mimir.JsonDecode as JSONDependency
private
  module JSON = JSONDependency floatConversion
import Mimir.JsonFlow as Flow
import Mimir.JsonCompletion as CompletionDependency
private
  module Completion = CompletionDependency floatConversion
import Mimir.SchemaDocument as SchemaDependency
private
  module Schema = SchemaDependency floatConversion
import Mimir.UnicodeText as Unicode
import Mimir.UnicodeCursorBytes as Cursor
import Mimir.JsonDiagnosticCode as Diagnostic
import Mimir.JsonDiagnostics as DiagnosticsDependency
private
  module Diagnostics = DiagnosticsDependency floatConversion
import Mimir.SignedMachine as Machine

module F = Flow.F
module Messages = Diagnostics.Parser Machine.disabled

data Result (input : List Byte) : Set where
  accepted : Schema.Document → (position : F.Cursor input) → F.Cursor.remaining position ≡ [] → Result input
  rejected : (failure : F.Rejected input) → Diagnostic.Rejection failure → Result input

classify : ∀ {input} (result : Flow.Result JSON.Decoded input) →
  Completion.Complete result → Ordinary.Normal result → Diagnostic.Safe result → Result input
classify (Flow.panicked position) complete () safe
classify (Flow.ordinary (F.failure failure)) complete ordinary safe = rejected failure safe
classify (Flow.ordinary (F.success parsedDocument position)) complete ordinary safe = accepted (Schema.build parsedDocument) position complete

read : ∀ input → Result input
read input = classify (Flow.Productive.result (Ordinary.D.read input))
  (Ordinary.D.consumesCompleteDocument input) (Ordinary.decodedDocument input) (Messages.decodedDocument input)

data StringResult (text : Text) : Set where
  invalidScalar : ¬ Unicode.Valid text → StringResult text
  admitted : (valid : Unicode.Valid text) → Result (Cursor.encoded text valid) → StringResult text

readString : ∀ text → StringResult text
readString text with Unicode.valid? text
... | no invalid = invalidScalar invalid
... | yes valid = admitted valid (read (Cursor.encoded text valid))

-- Rust string inputs already have this admission evidence. This entry point
-- performs no text normalization and cannot take the invalid-scalar branch.
readAdmitted : ∀ text (valid : Unicode.Valid text) → Result (Cursor.encoded text valid)
readAdmitted text valid = read (Cursor.encoded text valid)
