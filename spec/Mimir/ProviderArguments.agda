{-# OPTIONS --safe #-}
-- Instantiate the provider envelopes with concrete UTF-8/JSON argument
-- decoding with an explicit numeric-conversion dependency. Ordinary argument
-- errors retain the exact parser diagnostic rather than a generic replacement.
import Mimir.FloatConversion
module Mimir.ProviderArguments (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.Validation using (Fault; problem; fault; malformedInput)
import Mimir.StructuredValue as Value
import Mimir.SchemaDocument as SchemaDependency
private
  module Schema = SchemaDependency floatConversion
import Mimir.JsonReleaseDocument as JSONDependency
private
  module JSON = JSONDependency floatConversion
import Mimir.JsonDiagnosticCode as Diagnostic
import Mimir.JsonErrorDisplay as Display
import Mimir.UnicodeText as Unicode
import Mimir.ProviderResponse as Response
import Mimir.ProviderReplay as Replay
import Mimir.ProviderQueueAdmission as Admission

syntaxFailure : ∀ {input} (failure : JSON.F.Rejected input) → Diagnostic.Rejection failure → Fault
syntaxFailure failure safe with Diagnostic.renderAvailable failure safe
... | detail , exact = problem [] malformedInput detail

failureMessageExact : ∀ {input} (failure : JSON.F.Rejected input) safe →
  Display.renderRejected failure ≡ just (Fault.explanation (syntaxFailure failure safe))
failureMessageExact failure safe with Diagnostic.renderAvailable failure safe
... | detail , exact = exact

convert : ∀ {input} → JSON.Result input → Fault ⊎ Value.Value
convert (JSON.accepted parsedDocument position complete) = inj₂ (Schema.Document.value parsedDocument)
convert (JSON.rejected failure safe) = inj₁ (syntaxFailure failure safe)

decode : Text → Fault ⊎ Value.Value
decode text with Unicode.valid? text
... | no invalid = inj₁ (fault [] malformedInput "argument text contains a non-scalar character")
... | yes valid = convert (JSON.readAdmitted text valid)

-- Every admitted text selects its actual UTF-8/JSON path. The rejection for
-- non-scalar Agda characters cannot substitute for parsing a Rust string.
admittedUsesConcreteParser : ∀ text → Unicode.Valid text →
  Σ (Unicode.Valid text) (λ valid → decode text ≡ convert (JSON.readAdmitted text valid))
admittedUsesConcreteParser text admitted with Unicode.valid? text
... | no invalid = ⊥-elim (invalid admitted)
... | yes valid = valid , refl

acceptedValueUnchanged : ∀ {input} parsedDocument (position : JSON.F.Cursor input) complete →
  convert (JSON.accepted parsedDocument position complete) ≡ inj₂ (Schema.Document.value parsedDocument)
acceptedValueUnchanged parsedDocument position complete = refl

module Providers = Response.Decode decode
module Preservation = Replay.Replay decode
module QueueAdmission = Admission.Admission decode
