{-# OPTIONS --safe #-}
-- Concrete replacement semantics for McpExchange.handleTool. The only
-- completed-work constructor requires a decoded operation, its full run,
-- and the exact output projection. Corrections require rejected admission and
-- have no business events. No handler callback is assumed.
module Mimir.McpToolExecution where

open import Data.List using (List; []; _∷_)
import Data.List.Properties as List
open import Data.Nat using (ℕ; _≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Data.String using (toList)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Validation using (Fault; fault; key; unknownField)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.StructuredValue as V
import Mimir.ToolCatalog as T
import Mimir.McpEnvelope as Envelope
import Mimir.PublicRequest as Request
import Mimir.ApplicationProtocol as Application
import Mimir.ApplicationOutput as Output
import Mimir.PublicEncoding as Encoding
import Mimir.StandardLibrary as Conversion
import Mimir.McpErrors as Errors
import Mimir.GraphMutationProtocol as Mutation
import Mimir.ApplicationStore as Store
module Correction = Errors.AgentCorrection

all : List T.Tool
all = T.insertBelief ∷ T.deleteBelief ∷ T.deleteProject ∷ T.deletePattern ∷ T.insertPattern ∷
  T.recordSupport ∷ T.recordCause ∷ T.recordDefeat ∷ T.recordContradiction ∷
  T.getBelief ∷ T.listBeliefs ∷ T.listPatterns ∷ T.getContradictions ∷
  T.decayAll ∷ T.sweepExpiredDefeated ∷ T.queryRelevant ∷ T.addEvidence ∷ T.getEvidence ∷
  T.propagateFrom ∷ T.queryIntervention ∷ T.loadDocument ∷ T.queryDocument ∷ T.clearDocument ∷
  T.getLearningReview ∷ T.learningCapabilities ∷ T.getLessonAssessment ∷ T.lessonAssessmentHistory ∷
  T.explainBelief ∷ T.recordExperience ∷ T.pendingExperiences ∷ T.reviewExperience ∷
  T.getExperience ∷ T.experienceHistory ∷ T.queryLearningContext ∷
  T.reserveOperation ∷ T.operationOutcome ∷ T.cancelOperation ∷ []

find : Envelope.Text → List T.Tool → Maybe T.Tool
find name [] = nothing
find name (tool ∷ rest) with name ≟Text Envelope.literal (T.wireName tool)
... | yes _ = just tool
... | no _ = find name rest

lookup : Envelope.Text → Maybe T.Tool
lookup name = find name all

module Run (environment : Application.Environment) (format : Encoding.Formatting)
  (conversion : Conversion.Contract) where
  module A = Application.Run environment using (Result; Event; Runs; start)
  module P = Output.Project environment format using
    (project; success; failure; decision; boundReferenceDecision; partialDecision; partialValue; boundReferenceReport)
  module D = Request.Decode (Application.Environment.library environment) using (readInvocation)

  data Diagnostic : Set where
    operationFailed : A.Result → Diagnostic

  data Result : Set where
    failure : Diagnostic → Result
    inputCorrection : Correction.Claim → Result
    preparationDecision : A.Result → Correction.Claim → Result
    boundReferenceDecision : A.Result → Store.BindingRow → Fault → Result
    partialDecision : A.Result → Mutation.CommittedEdge → Correction.Claim → Result
    completed : V.Value → Result

  unknownTool : Envelope.Text → Correction.Claim
  unknownTool name = Correction.claim
    (Correction.item Correction.request
      (fault (key "name" ∷ []) unknownField "The requested tool is not registered.")
      (toList "A tool name advertised by tools/list.")
      (toList "Read the advertised tool names and choose the intended tool. If the intended operation is unclear, ask the user; do not guess a replacement.")) []

  invalidArguments : Fault → Correction.Claim
  invalidArguments detail = Correction.claim
    (Correction.item Correction.arguments detail
      (toList "The advertised required fields, field types and accepted alternatives.")
      (toList "Correct the indicated field using the tool schema and task context. If its value is unknown, ask the user; do not invent a default.")) []

  finish : A.Result → Result
  finish result with P.project result
  ... | P.success value = completed value
  ... | P.failure cause = failure (operationFailed cause)
  ... | P.decision report = preparationDecision result report
  ... | P.boundReferenceDecision binding detail = boundReferenceDecision result binding detail
  ... | P.partialDecision edge report = partialDecision result edge report

  data Handled (name : Envelope.Text) (raw : V.Value) : List A.Event → Result → Set where
    unknown : lookup name ≡ nothing → Handled name raw [] (inputCorrection (unknownTool name))
    invalid : ∀ tool fault → lookup name ≡ just tool → D.readInvocation tool raw ≡ inj₁ fault →
      Handled name raw [] (inputCorrection (invalidArguments fault))
    executed : ∀ tool initial events result → lookup name ≡ just tool →
      A.Runs (A.start tool raw initial) events result → Handled name raw events (finish result)

  record Operation (name : Envelope.Text) (raw : V.Value) (events : List A.Event) (value : V.Value) : Set where
    constructor operation
    field
      tool : T.Tool
      initial : Store.World
      result : A.Result
      named : lookup name ≡ just tool
      execution : A.Runs (A.start tool raw initial) events result
      projected : finish result ≡ completed value

  successWitness : ∀ name raw events reply value → Handled name raw events reply →
    reply ≡ completed value → Operation name raw events value
  successWitness name raw events reply value (executed tool initial events₁ result named ran) same =
    operation tool initial result named ran same

  successRequiresOperation : ∀ name raw events value → Handled name raw events (completed value) →
    Operation name raw events value
  successRequiresOperation name raw events value proof = successWitness name raw events (completed value) value proof refl

  completionCannotRequestCorrection : ∀ result report → finish result ≡ inputCorrection report → Data.Empty.⊥
  completionCannotRequestCorrection result report with P.project result
  ... | P.success value = λ ()
  ... | P.failure cause = λ ()
  ... | P.decision report₁ = λ ()
  ... | P.boundReferenceDecision binding detail = λ ()
  ... | P.partialDecision edge report₁ = λ ()

  correctionWitness : ∀ name raw events reply report → Handled name raw events reply →
    reply ≡ inputCorrection report → events ≡ []
  correctionWitness name raw events reply report (unknown named) same = refl
  correctionWitness name raw events reply report (invalid tool detail named decoded) same = refl
  correctionWitness name raw events reply report (executed tool initial events₁ result named ran) same =
    ⊥-elim (completionCannotRequestCorrection result report same)

  admissionCorrectionsHaveNoEvents : ∀ name raw events report →
    Handled name raw events (inputCorrection report) → events ≡ []
  admissionCorrectionsHaveNoEvents name raw events report proof =
    correctionWitness name raw events (inputCorrection report) report proof refl
