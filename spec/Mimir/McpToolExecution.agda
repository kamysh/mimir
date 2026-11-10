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
import Mimir.ApplicationHost as Host
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
    (Projection; project; success; failure; decision; boundReferenceDecision; partialDecision; partialValue; boundReferenceReport; globallyStoppedReadback)
  module D = Request.Decode (Application.Environment.library environment) using (readInvocation)
  module Physical = Host.Run environment

  data Diagnostic : Set where
    operationFailed : A.Result → Diagnostic
    physicalCleanupPending : Envelope.Text → A.Result → Store.World → Diagnostic

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

  finishProjection : A.Result → P.Projection → Result
  finishProjection original (P.success value) = completed value
  finishProjection original (P.failure cause) = failure (operationFailed cause)
  finishProjection original (P.decision report) = preparationDecision original report
  finishProjection original (P.boundReferenceDecision binding detail) = boundReferenceDecision original binding detail
  finishProjection original (P.partialDecision edge report) = partialDecision original edge report

  finish : A.Result → Result
  finish result = finishProjection result (P.project result)

  exitProjection : ∀ {selected before entered final}
    (entry : Physical.Entry selected before entered) (original : A.Result) →
    Physical.Exit entry (Physical.A.reached original) final → P.Projection
  exitProjection (Physical.ordinaryEntry before) original (Physical.ordinaryExit .before _) = P.project original
  exitProjection (Physical.fenced token before fence) original (Physical.fencedExit .token .before .fence _) = P.project original
  exitProjection (Physical.unknown token before absent) original (Physical.unknownExit .token .before .absent _) = P.project original
  exitProjection (Physical.started token row before entered same pending registered) original
    (Physical.acknowledged .token .row .before .entered .same .pending .registered _ ownedWorkers receipt timestamp) = P.project original
  exitProjection (Physical.cancelEntry token before) original
    (Physical.cancelExit .token .before _ final (Physical.unfenced noFinal noCancellation)) = P.project original
  exitProjection (Physical.cancelEntry token before) original
    (Physical.cancelExit .token .before _ final (Physical.allCopiesStopped receipt)) =
      P.globallyStoppedReadback original token receipt

  hostProjection : ∀ {tool raw events} → Physical.Execution tool raw events → P.Projection
  hostProjection execution = exitProjection (Physical.Execution.entry execution)
    (Physical.Execution.databaseResult execution) (Physical.Execution.exited execution)

  finishHosted : ∀ {tool raw events} → Physical.Result tool raw events → Result
  finishHosted (Physical.returned execution) = finishProjection
    (Physical.Execution.databaseResult execution) (hostProjection execution)
  finishHosted (Physical.cleanupPending initial entered entry databaseResult ran final pending) =
    failure (physicalCleanupPending (Physical.pendingReason pending) databaseResult final)

  data Handled (name : Envelope.Text) (raw : V.Value) : List A.Event → Result → Set where
    unknown : lookup name ≡ nothing → Handled name raw [] (inputCorrection (unknownTool name))
    invalid : ∀ tool fault → lookup name ≡ just tool → D.readInvocation tool raw ≡ inj₁ fault →
      Handled name raw [] (inputCorrection (invalidArguments fault))
    executed : ∀ tool events (hosted : Physical.Result tool raw events) → lookup name ≡ just tool →
      Handled name raw events (finishHosted hosted)

  -- Native handleTool futures own their registration while still pending.
  -- The transport derives shutdown rows from these actual started entries.
  record InFlight (name : Envelope.Text) (raw : V.Value) : Set where
    field
      tool : T.Tool
      named : lookup name ≡ just tool
      active : Physical.Active tool raw
    owned : List Store.ExecutionRow
    owned = Physical.Active.owned active

  record Operation (name : Envelope.Text) (raw : V.Value) (events : List A.Event) (value : V.Value) : Set where
    constructor operation
    field
      tool : T.Tool
      hosted : Physical.Execution tool raw events
      named : lookup name ≡ just tool
      projected : finishHosted (Physical.returned hosted) ≡ completed value

  successWitness : ∀ name raw events reply value → Handled name raw events reply →
    reply ≡ completed value → Operation name raw events value
  successWitness name raw events reply value (executed tool events₁ (Physical.returned hosted) named) same =
    operation tool hosted named same
  successWitness name raw events reply value
    (executed tool events₁ (Physical.cleanupPending initial entered entry databaseResult ran final pending) named) ()

  successRequiresOperation : ∀ name raw events value → Handled name raw events (completed value) →
    Operation name raw events value
  successRequiresOperation name raw events value proof = successWitness name raw events (completed value) value proof refl

  projectionCannotRequestCorrection : ∀ result projection report →
    finishProjection result projection ≡ inputCorrection report → Data.Empty.⊥
  projectionCannotRequestCorrection result (P.success value) report = λ ()
  projectionCannotRequestCorrection result (P.failure cause) report = λ ()
  projectionCannotRequestCorrection result (P.decision decision) report = λ ()
  projectionCannotRequestCorrection result (P.boundReferenceDecision binding detail) report = λ ()
  projectionCannotRequestCorrection result (P.partialDecision edge decision) report = λ ()

  correctionWitness : ∀ name raw events reply report → Handled name raw events reply →
    reply ≡ inputCorrection report → events ≡ []
  correctionWitness name raw events reply report (unknown named) same = refl
  correctionWitness name raw events reply report (invalid tool detail named decoded) same = refl
  correctionWitness name raw events reply report (executed tool events₁ (Physical.returned hosted) named) same =
    ⊥-elim (projectionCannotRequestCorrection (Physical.Execution.databaseResult hosted) (hostProjection hosted) report same)
  correctionWitness name raw events reply report
    (executed tool events₁ (Physical.cleanupPending initial entered entry databaseResult ran final pending) named) ()

  admissionCorrectionsHaveNoEvents : ∀ name raw events report →
    Handled name raw events (inputCorrection report) → events ≡ []
  admissionCorrectionsHaveNoEvents name raw events report proof =
    correctionWitness name raw events (inputCorrection report) report proof refl
