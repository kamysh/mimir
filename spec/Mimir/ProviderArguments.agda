{-# OPTIONS --safe #-}
-- Provider arguments use the standard JSON reader. Mimir retains the exact
-- supplied diagnostic and the original ordered provider-call structure.
import Mimir.StandardLibrary
module Mimir.ProviderArguments (library : Mimir.StandardLibrary.Contract) where

open import Data.List using ([])
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.Validation using (Fault; problem; malformedInput)
import Mimir.StandardLibrary as Library
import Mimir.StructuredValue as Value
import Mimir.ProviderResponse as Response
import Mimir.ProviderReplay as Replay
import Mimir.ProviderQueueAdmission as Admission

syntaxFailure : Library.JSONError → Fault
syntaxFailure error = problem [] malformedInput (Library.JSONError.message error)

failureMessageExact : ∀ error →
  Fault.explanation (syntaxFailure error) ≡ Library.JSONError.message error
failureMessageExact error = refl

convert : Library.JSONResult → Fault ⊎ Value.Value
convert (Library.parsed value) = inj₂ value
convert (Library.rejected error) = inj₁ (syntaxFailure error)
convert (Library.panicked message) = inj₁ (problem [] malformedInput message)

decode : Text → Fault ⊎ Value.Value
decode text = convert (Library.Contract.jsonValue library (Library.Contract.encodeUTF8 library text))

acceptedValueUnchanged : ∀ value → convert (Library.parsed value) ≡ inj₂ value
acceptedValueUnchanged value = refl

module Providers = Response.Decode decode
module Preservation = Replay.Replay decode
module QueueAdmission = Admission.Admission decode
