{-# OPTIONS --safe #-}
-- Composed wire-to-schema decoding. Syntax errors, schema errors and native
-- panics remain distinct; successful typed results carry decoder evidence and
-- complete input consumption. Numeric conversion is an explicit dependency
-- parameter; native conversion correspondence is not established here.
import Mimir.FloatConversion
module Mimir.SchemaDocument (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.List using (List; [])
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Bits using (Byte)
open import Mimir.Validation using (Fault)
import Mimir.JsonDecode as JSONDependency
private
  module JSON = JSONDependency floatConversion
import Mimir.JsonStoredValue as Stored
import Mimir.JsonSchemaValue as Convert
import Mimir.StructuredValue as Schema
import Mimir.JsonFlow as Flow
import Mimir.JsonCompletion as CompletionDependency
private
  module Completion = CompletionDependency floatConversion
import Mimir.SignedMachine as Machine

module F = Flow.F

record Document : Set where
  constructor document
  field
    parsed : JSON.Decoded
    value : Schema.Value
    exact : value ≡ Convert.convert (JSON.Decoded.value parsed) (JSON.Decoded.canonical parsed)
    represents : Convert.Represents (JSON.Decoded.value parsed) value

build : JSON.Decoded → Document
build parsed = document parsed (Convert.convert (JSON.Decoded.value parsed) (JSON.Decoded.canonical parsed)) refl
  (Convert.conversionRepresents (JSON.Decoded.value parsed) (JSON.Decoded.canonical parsed))

module Typed {Value : Set} (decode : Schema.Value → Fault ⊎ Value) where
  record Accepted : Set where
    constructor accepted
    field
      source : Document
      value : Value
      observed : decode (Document.value source) ≡ inj₂ value

  record Rejected : Set where
    constructor rejected
    field
      source : Document
      failure : Fault
      observed : decode (Document.value source) ≡ inj₁ failure

  data Result (input : List Byte) : Set where
    accepted : Accepted → (position : F.Cursor input) → F.Cursor.remaining position ≡ [] → Result input
    rejected : Rejected → (position : F.Cursor input) → F.Cursor.remaining position ≡ [] → Result input
    syntaxError : F.Rejected input → Result input
    panicked : F.Cursor input → Result input

  validate : ∀ {input} → Document → (position : F.Cursor input) → F.Cursor.remaining position ≡ [] → Result input
  validate source position complete with decode (Document.value source) in observed
  ... | inj₁ failure = rejected (rejected source failure observed) position complete
  ... | inj₂ value = accepted (accepted source value observed) position complete

  fromJSON : ∀ {input} (result : Flow.Result JSON.Decoded input) → Completion.Complete result → Result input
  fromJSON (Flow.panicked position) complete = panicked position
  fromJSON (Flow.ordinary (F.failure failure)) complete = syntaxError failure
  fromJSON (Flow.ordinary (F.success value position)) complete = validate (build value) position complete

  module Parser (checks : Machine.OverflowChecks) where
    module P = JSON.Parser checks
    read : ∀ input → Result input
    read input = fromJSON (Flow.Productive.result (P.read input)) (P.consumesCompleteDocument input)
