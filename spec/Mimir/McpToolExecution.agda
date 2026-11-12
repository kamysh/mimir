{-# OPTIONS --safe #-}
-- A successful tool reply comes from a guarded application operation.
module Mimir.McpToolExecution where

open import Data.List using (List; []; _∷_)
import Data.List.Properties as List
open import Data.Nat using (ℕ; _≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Mimir.Validation using (Fault)
import Mimir.Validation as Validation
open import Mimir.SourceReview using (_≟Text_)
import Mimir.StructuredValue as V
open import Mimir.Text using (Text)
import Mimir.ToolCatalog as T
import Mimir.McpEnvelope as Envelope
import Mimir.PublicRequest as Request
import Mimir.ApplicationProtocol as Application
import Mimir.ApplicationStore as Store
import Mimir.GraphMutationProtocol as Mutation
import Mimir.BeliefEmbedding as BeliefEmbedding
import Mimir.Reembedding as Reembedding
import Mimir.InferenceProtocol as Inference
open import Mimir.UUIDGroups using (UUID)
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
    using (Event; GuardedRuns; Result; invalidGrounding; invalidRequestIdentity;
      mutated; needsDecision; reembeddingResult; startRequest)
  module P = Output.Project environment format using (project; success; failure)
  module D = Request.Decode conversion

  data Diagnostic : Set where
    unknownTool : Envelope.Text → Diagnostic
    invalidArguments : Fault → Diagnostic
    operationFailed : A.Result → Diagnostic
    userDecisionRequired : Text → Text → Diagnostic

  Result = Diagnostic ⊎ V.Value


  finish : A.Result → Result
  finish (A.reembeddingResult (Reembedding.needsDecision reason guidance)) = inj₁ (userDecisionRequired reason guidance)
  finish (A.needsDecision reason guidance) = inj₁ (userDecisionRequired reason guidance)
  finish A.invalidRequestIdentity = inj₁ (invalidArguments
    (Validation.fault (Validation.key "id" ∷ []) Validation.wrongIdentity
      "Request ID must be a string. Use a non-numeric ID and retry."))
  finish (A.mutated (Mutation.embeddingFailed (BeliefEmbedding.needsInput reason guidance))) =
    inj₁ (userDecisionRequired reason guidance)
  finish (A.mutated Mutation.invalidPatternRate) = inj₁ (invalidArguments
    (Validation.fault (Validation.key "success_rate" ∷ []) Validation.invalidNumber
      "success_rate must be between 0 and 1"))
  finish (A.mutated Mutation.invalidEdgeWeight) = inj₁ (invalidArguments
    (Validation.fault (Validation.key "weight" ∷ []) Validation.invalidNumber
      "weight must be between 0 and 1"))
  finish A.invalidGrounding = inj₁ (invalidArguments
    (Validation.fault (Validation.key "weight" ∷ []) Validation.invalidNumber
      "weight must be between 0 and 1"))
  finish (A.mutated Mutation.invalidOrigin) = inj₁ (invalidArguments
    (Validation.fault (Validation.key "provenance" ∷ []) Validation.unsupportedCombination
      "Cite an independent user instruction or document. Use record_experience for claims derived from an incident."))
  finish result with P.project result
  ... | P.success value = inj₂ value
  ... | P.failure cause = inj₁ (operationFailed cause)

  data Handled (identityValue : Envelope.Identity) (name : Envelope.Text) (raw : V.Value)
    (before : Store.World) : List A.Event → Result → Store.World → Set where
    unknown : lookup name ≡ nothing → Handled identityValue name raw before [] (inj₁ (unknownTool name)) before
    invalid : ∀ tool fault → lookup name ≡ just tool → D.readTool tool raw ≡ inj₁ fault →
      Handled identityValue name raw before [] (inj₁ (invalidArguments fault)) before

    executed : ∀ tool request events result after → lookup name ≡ just tool → D.readTool tool raw ≡ inj₂ request →
      A.GuardedRuns (A.startRequest identityValue name raw request) before events after result →
      Handled identityValue name raw before events (finish result) after


  record Operation (identityValue : Envelope.Identity) (name : Envelope.Text) (raw : V.Value)
    (before : Store.World) (events : List A.Event) (value : V.Value) (after : Store.World) : Set where
    constructor operation
    field
      tool : T.Tool
      request : Request.Request
      result : A.Result
      named : lookup name ≡ just tool
      decoded : D.readTool tool raw ≡ inj₂ request
      execution : A.GuardedRuns (A.startRequest identityValue name raw request) before events after result
      projected : finish result ≡ inj₂ value

  data Success (identityValue : Envelope.Identity) (name : Envelope.Text) (raw : V.Value)
    (before : Store.World) : List A.Event → V.Value → Store.World → Set where
    executed : ∀ events value after → Operation identityValue name raw before events value after →
      Success identityValue name raw before events value after

  successWitness : ∀ identityValue name raw before events reply value after → Handled identityValue name raw before events reply after →
    reply ≡ inj₂ value → Success identityValue name raw before events value after
  successWitness identityValue name raw before events reply value after (executed tool request events₁ result .after named decoded ran) same =
    executed events value after (operation tool request result named decoded ran same)

  successHasSource : ∀ identityValue name raw before events value after → Handled identityValue name raw before events (inj₂ value) after →
    Success identityValue name raw before events value after
  successHasSource identityValue name raw before events value after proof =
    successWitness identityValue name raw before events (inj₂ value) value after proof refl
