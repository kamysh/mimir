{-# OPTIONS --safe #-}
-- Concrete replacement semantics for McpExchange.handleTool. The only
-- successful reply constructor requires a decoded operation, its full run,
-- and the exact application output projection. No handler callback is assumed.
module Mimir.McpToolExecution where

open import Data.List using (List; []; _∷_)
import Data.List.Properties as List
open import Data.Nat using (ℕ; _≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Validation using (Fault)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.StructuredValue as V
import Mimir.ToolCatalog as T
import Mimir.McpEnvelope as Envelope
import Mimir.PublicRequest as Request
import Mimir.ApplicationProtocol as Application
import Mimir.ApplicationOutput as Output
import Mimir.PublicEncoding as Encoding
import Mimir.StandardLibrary as Conversion

all : List T.Tool
all = T.insertBelief ∷ T.deleteBelief ∷ T.deleteProject ∷ T.deletePattern ∷ T.insertPattern ∷
  T.recordSupport ∷ T.recordCause ∷ T.recordDefeat ∷ T.recordContradiction ∷
  T.getBelief ∷ T.listBeliefs ∷ T.listPatterns ∷ T.getContradictions ∷
  T.decayAll ∷ T.sweepExpiredDefeated ∷ T.queryRelevant ∷ T.addEvidence ∷ T.getEvidence ∷
  T.propagateFrom ∷ T.queryIntervention ∷ T.loadDocument ∷ T.queryDocument ∷ T.clearDocument ∷
  T.getLearningReview ∷ T.learningCapabilities ∷ T.getLessonAssessment ∷ T.lessonAssessmentHistory ∷
  T.explainBelief ∷ T.recordExperience ∷ T.pendingExperiences ∷ T.reviewExperience ∷
  T.getExperience ∷ T.experienceHistory ∷ T.queryLearningContext ∷ []

find : Envelope.Text → List T.Tool → Maybe T.Tool
find name [] = nothing
find name (tool ∷ rest) with name ≟Text Envelope.literal (T.wireName tool)
... | yes _ = just tool
... | no _ = find name rest

lookup : Envelope.Text → Maybe T.Tool
lookup name = find name all

module Run (environment : Application.Environment) (format : Encoding.Formatting)
  (conversion : Conversion.Contract) where
  module A = Application.Run environment
  module P = Output.Project environment format
  module D = Request.Decode conversion

  data Diagnostic : Set where
    unknownTool : Envelope.Text → Diagnostic
    invalidArguments : Fault → Diagnostic
    operationFailed : A.Result → Diagnostic

  Result = Diagnostic ⊎ V.Value

  finish : A.Result → Result
  finish result with P.project result
  ... | P.success value = inj₂ value
  ... | P.failure cause = inj₁ (operationFailed cause)

  data Handled (name : Envelope.Text) (raw : V.Value) : List A.Event → Result → Set where
    unknown : lookup name ≡ nothing → Handled name raw [] (inj₁ (unknownTool name))
    invalid : ∀ tool fault → lookup name ≡ just tool → D.readTool tool raw ≡ inj₁ fault →
      Handled name raw [] (inj₁ (invalidArguments fault))
    executed : ∀ tool request events result → lookup name ≡ just tool → D.readTool tool raw ≡ inj₂ request →
      A.Runs (A.start request) events result → Handled name raw events (finish result)

  record Operation (name : Envelope.Text) (raw : V.Value) (events : List A.Event) (value : V.Value) : Set where
    constructor operation
    field
      tool : T.Tool
      request : Request.Request
      result : A.Result
      named : lookup name ≡ just tool
      decoded : D.readTool tool raw ≡ inj₂ request
      execution : A.Runs (A.start request) events result
      projected : finish result ≡ inj₂ value

  successWitness : ∀ name raw events reply value → Handled name raw events reply →
    reply ≡ inj₂ value → Operation name raw events value
  successWitness name raw events reply value (executed tool request events₁ result named decoded ran) same =
    operation tool request result named decoded ran same

  successRequiresOperation : ∀ name raw events value → Handled name raw events (inj₂ value) →
    Operation name raw events value
  successRequiresOperation name raw events value proof = successWitness name raw events (inj₂ value) value proof refl
