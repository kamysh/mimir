{-# OPTIONS --safe #-}
-- Concrete operation kinds determine their inputs, replies and business
-- goals. There is no caller-selected goal, script or physical relation here.
module Mimir.PublicOperationCatalogue where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Float.Base using (Float)
open import Data.Integer using (ℤ)
open import Data.List using (List; [])
import Data.Maybe
open import Data.Nat using (ℕ; zero; suc; s≤s; z≤n)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.PublicRequest as Public
import Mimir.StandardLibrary as Library
import Mimir.PublicEncoding as Encoding
import Mimir.PosteriorComputation as Posterior
import Mimir.RetrievalRanking as Ranking
import Mimir.StorageReadBinding as Database
import Mimir.LearningQueryBinding as LearningReads
import Mimir.InferenceStorageBinding as Inference
import Mimir.ConfigurationValues as Config
import Mimir.Recovery as Recovery
import Mimir.PublicOperationBinding as Binding
import Mimir.ToolCatalog as Tools
import Mimir.ProjectDeletion as Project
import Mimir.PatternPublicationRecovery as Pattern
import Mimir.PublicPatternDeletionRecovery as DeletePattern
import Mimir.DirectGraphRecovery as Edges
import Mimir.BeliefDeletionRecovery as DeleteBelief
import Mimir.GroundingRecovery as Ground
import Mimir.PropagationRecovery as Propagation
import Mimir.DecayRecovery as Decay
import Mimir.DocumentRemovalRecovery as Clear
import Mimir.StructuredValue as Wire
import Mimir.Validation as Validation
import Mimir.RecoverableStoreStep as Step
import Mimir.PublicRetrievalRecovery as Search
import Mimir.PublicLearningContextRecovery as Context
import Mimir.PublicDocumentQueryRecovery as Documents
import Mimir.Effects as Effects
import Mimir.IndependentPublicationRecovery as Independent
import Mimir.IndependentBeliefRecovery as IndependentIntent
import Mimir.GraphReadProtocol as GraphRead
import Mimir.LearningQueryProtocol as LearningQuery
import Mimir.DefeatRecovery as Defeat
import Mimir.SweepRecovery as Sweep
import Mimir.ExperienceSourceRecovery as Source
import Mimir.DocumentLoadingRecovery as Loading
import Mimir.ReviewOperationRecovery as ReviewOperation
import Mimir.ReviewPublicationRecovery as ReviewPublication
import Mimir.ReviewPreparationRecovery as ReviewPreparation
import Mimir.OperationControls as Controls
import Mimir.GraphMutationProtocol as Mutation
import Mimir.GraphDeletion as Deletion
import Mimir.InferenceProtocol as InferenceRequest
import Mimir.LearningOperations as Learning
import Mimir.ReviewSchema as Relations
import Mimir.DocumentQuery as DocumentAnswer

-- A fixed request is supplied by the closed dispatcher. This reindexing
-- preserves the original script, physical semantics and whole-world goal.
module Reindex {Input Selected Result : Set} {Goal : Input → Store.World → Store.World → Result → Set}
  (original : Recovery.RecoverableFor Store.World Input Result Goal) (request : Selected → Input) where
  module O = Recovery.RecoverableFor original
  Meaning : Selected → Store.World → Store.World → Result → Set
  Meaning selected = Goal (request selected)
  operation : Recovery.RecoverableFor Store.World Selected Result Meaning
  operation = record
    { Effect = O.Effect; Reply = O.Reply; script = λ selected → O.script (request selected); Atomic = O.Atomic
    ; converges = λ selected → O.converges (request selected); progress = λ selected → O.progress (request selected) }

module Fixed {Input Result : Set} {Goal : Input → Store.World → Store.World → Result → Set}
  (original : Recovery.RecoverableFor Store.World Input Result Goal) (request : Input) =
  Reindex original (λ (_ : ⊤) → request)

-- A rejected internal request has no database or provider effects. Its
-- diagnostic is fixed by request classification, before execution begins.
module Refusal (diagnostic : Validation.Fault) where
  Reply : ⊥ → Set
  Reply = ⊥-elim
  module E = Effects.Protocol ⊥ Reply
  Atomic : Store.World → (effect : ⊥) → Reply effect → Store.World → Set
  Atomic before ()
  module X = Recovery.Execution Store.World ⊥ Reply Atomic
  script : ⊤ → E.Script Validation.Fault
  script _ = E.done diagnostic
  Goal : ⊤ → Store.World → Store.World → Validation.Fault → Set
  Goal _ before after result = after ≡ before × result ≡ diagnostic
  interruptedUnchanged : ∀ initial final → X.Interrupted (script tt) initial final → final ≡ initial
  interruptedUnchanged initial .initial (X.atPrefix .[] .(E.done diagnostic) .initial (E.stopped _) (X.unchanged _)) = refl
  interruptedUnchanged initial final (X.beforeReply _ () _ _ _ _ _ _ _)
  converges : ∀ input initial interrupted final result → X.Interrupted (script input) initial interrupted →
    X.Completed (script input) interrupted final result → Goal input initial final result
  converges tt initial interrupted .interrupted .diagnostic crash (X.completed .[] (E.returned _) (X.unchanged _)) =
    interruptedUnchanged initial interrupted crash , refl
  operation : Recovery.RecoverableFor Store.World ⊤ Validation.Fault Goal
  operation = record
    { Effect = ⊥; Reply = Reply; script = script; Atomic = Atomic; converges = converges
    ; progress = λ _ initial → initial , diagnostic , X.completed [] (E.returned _) (X.unchanged initial) }

module BindingFrame {Effect : Set} {Reply : Effect → Set}
  (Atomic : Store.World → (effect : Effect) → Reply effect → Store.World → Set)
  (atomicKeeps : ∀ before effect reply after → Atomic before effect reply after →
    Binding.bindings after ≡ Binding.bindings before) where
  module X = Recovery.Execution Store.World Effect Reply Atomic
  changesKeep : ∀ {before events after} → X.Changes before events after → Binding.bindings after ≡ Binding.bindings before
  changesKeep (X.unchanged _) = refl
  changesKeep (X.changed before effect reply middle physical later) =
    trans (changesKeep later) (atomicKeeps before effect reply middle physical)
  interruptedKeeps : ∀ {Result} (script : X.E.Script Result) before after →
    X.Interrupted script before after → Binding.bindings after ≡ Binding.bindings before
  interruptedKeeps script before after (X.atPrefix _ _ _ _ physical) = changesKeep physical
  interruptedKeeps script before after (X.beforeReply _ effect _ middle reply _ _ previous active) =
    trans (atomicKeeps middle effect reply after active) (changesKeep previous)
  existingBindingSurvives : ∀ {Result} (script : X.E.Script Result) token before after original →
    Project.Registered.binding token (Binding.bindings before) ≡ Data.Maybe.just original →
    X.Interrupted script before after → Project.Registered.binding token (Binding.bindings after) ≡ Data.Maybe.just original
  existingBindingSurvives script token before after original present crash =
    trans (cong (Project.Registered.binding token) (interruptedKeeps script before after crash)) present

module Run (library : Library.Contract) (format : Encoding.Formatting)
  (databaseSum : List Float → Float) (calculator : Posterior.Calculator)
  (arithmetic : Ranking.F32) (unicode : Ranking.Unicode)
  (vectors : Database.VectorOperations) (configuration : Config.Config)
  (textBefore : Text → Text → Bool)
  (allocateOwner : ℕ → Store.World → IndependentIntent.Allocation)
  (database : ℕ) (postgres : Controls.PostgreSQL)
  (serverTime : ℕ → Store.World → ℤ)
  (utcTimestamp : Text → Validation.Fault Data.Sum.⊎ ℤ)
  (sourcePostgres : Source.PostgreSQL)
  (sweepObservation : ℕ → Store.World → Sweep.Metadata)
  (reviewDependencies : ReviewPublication.Dependencies)
  (reviewCodec : ReviewPreparation.AllocationEncoding.Codec format)
  (reviewBackend : Store.World → ReviewPublication.Preparing.Claim → Text Data.Sum.⊎ List Store.Vector) where
  module Admit = Binding.Decode library
  module Request = Public.Decode library
  module Basic = Database.BasicReads format
  module Experiences = LearningReads.ExperienceReads format
  module Assessments = LearningReads.AssessmentReads format
  module Intervention = Inference.InterventionRecovery databaseSum calculator
  module Retrieval = Search.Run arithmetic unicode vectors configuration
  module LearningContext = Context.Run arithmetic unicode vectors configuration textBefore
  module DocumentQuery = Documents.Run vectors configuration
  module PatternWrite = Pattern.Registered library format
  module PatternRemoval = DeletePattern.Registered library
  module Relationship kind = Edges.Registered library kind
  module BeliefRemoval = DeleteBelief.Registered library databaseSum calculator serverTime
  module Grounding kind = Ground.Registered kind library databaseSum calculator serverTime
  module Propagate = Propagation.Registered format library databaseSum calculator serverTime
  module Decaying = Decay.Registered library databaseSum serverTime
  module DocumentRemoval = Clear.Registered library databaseSum calculator serverTime
  module IndependentWrite = Independent.Registered format library databaseSum calculator allocateOwner
  module IndependentPublic = IndependentWrite.Public configuration
  module Defeating = Defeat.Registered library databaseSum calculator serverTime
  module Sweeping = Sweep.Registered library format databaseSum calculator sweepObservation
  module Recording = Source.Registered library format database databaseSum calculator sourcePostgres
  module DocumentEntry = Loading.Registered.Entry library format utcTimestamp databaseSum calculator serverTime configuration postgres
    using (Outcome; inspected; executed; normalized; EntryGoal; Operation; fullOperation; toRecoverable)
  module Reviewing = ReviewOperation.Registered library format database databaseSum calculator
    reviewDependencies reviewCodec postgres reviewBackend
    using (Result; Goal; operation)
  ReviewEnvironment : Set
  ReviewEnvironment = ReviewPreparation.Registered.Environment library format database databaseSum calculator
    reviewDependencies reviewCodec postgres
  module Control = Controls.Controls library postgres
  module ControlFixed request input = Fixed (Control.operation request) input
  module ProjectIntent = Recovery.DeterministicContract Project.Registered.recoverable
  module ProjectSelected project = Reindex ProjectIntent.operationFor (λ token → Project.Registered.input token project)

  module BasicIntent = Recovery.DeterministicContract Basic.operation
  module ExperienceIntent = Recovery.DeterministicContract Experiences.operation
  module AssessmentIntent = Recovery.DeterministicContract Assessments.operation
  module BasicFixed request = Fixed BasicIntent.operationFor request
  module ExperienceFixed request = Fixed ExperienceIntent.operationFor request
  module AssessmentFixed request = Fixed AssessmentIntent.operationFor request
  module InterventionFixed request = Fixed Intervention.operation request
  module RetrievalFixed request = Fixed (Retrieval.toRecoverable Retrieval.operation) request
  module ContextFixed request = Fixed (LearningContext.toRecoverable LearningContext.operation) request
  module DocumentFixed request = Fixed (DocumentQuery.toRecoverable DocumentQuery.fullOperation) request

  module PatternFrame = Binding.AdmittedStep PatternWrite.Internal Validation.Fault proj₁
    (λ input → PatternWrite.key (proj₁ input)) (λ input → PatternWrite.distinct (proj₁ input))
    PatternWrite.decide PatternWrite.keepsJournal PatternWrite.admit

  patternBinding : ∀ token before interrupted original →
    Project.Registered.binding token (Binding.bindings before) ≡ Data.Maybe.just original →
    PatternWrite.X.Interrupted (PatternWrite.script token) before interrupted →
    Project.Registered.binding token (Binding.bindings interrupted) ≡ Data.Maybe.just original
  patternBinding token before interrupted original present crash with PatternWrite.interruptionState token before interrupted crash
  ... | inj₁ same = trans (cong (λ state → Project.Registered.binding token (Binding.bindings state)) same) present
  ... | inj₂ (metadata , same) = trans
    (cong (λ state → Project.Registered.binding token (Binding.bindings state)) same)
    (trans (cong (Project.Registered.binding token) (PatternFrame.bindingsUnchanged (token , metadata) before)) present)

  module PatternGuard expected = Admit.Guarded (Binding.advertised Tools.insertPattern) expected PatternWrite.operation patternBinding

  module PatternRemovalFrame = Binding.AdmittedStep ℕ Validation.Fault (λ token → token) PatternRemoval.key
    PatternRemoval.distinct PatternRemoval.decide PatternRemoval.keepsJournal PatternRemoval.admit
  module PatternRemovalGuard expected = Admit.Guarded (Binding.advertised Tools.deletePattern) expected PatternRemoval.operation
    (λ token → PatternRemovalFrame.existingBindingSurvives token token)

  module RelationshipFrame kind = Binding.AdmittedStep ℕ Validation.Fault (λ token → token) (Relationship.key kind)
    (Relationship.distinct kind) (Relationship.decide kind) (Relationship.keepsJournal kind) (Relationship.admit kind)
  relationshipTool : Edges.Kind → Tools.Tool
  relationshipTool Edges.support = Tools.recordSupport
  relationshipTool Edges.cause = Tools.recordCause
  relationshipTool Edges.contradiction = Tools.recordContradiction
  module RelationshipGuard kind expected = Admit.Guarded (Binding.advertised (relationshipTool kind)) expected (Relationship.operation kind)
    (λ token → RelationshipFrame.existingBindingSurvives kind token token)

  registrationKeepsBinding : ∀ token before after original → Step.registration after ≡ Step.registration before →
    Project.Registered.binding token (Binding.bindings before) ≡ just original →
    Project.Registered.binding token (Binding.bindings after) ≡ just original
  registrationKeepsBinding token before after original unchanged present = trans
    (cong (λ registration → Project.Registered.binding token (proj₁ (proj₂ (proj₂ registration)))) unchanged) present

  module BeliefRemovalGuard expected = Admit.Guarded (Binding.advertised Tools.deleteBelief) expected BeliefRemoval.operation
    (λ token before after original present crash → registrationKeepsBinding token before after original
      (BeliefRemoval.interruptedKeepsRegistration token before after crash) present)

  groundingSource : Ground.Kind → Binding.Source
  groundingSource Ground.addition = Binding.advertised Tools.addEvidence
  groundingSource Ground.removal = Binding.evidenceRemoval
  module GroundingGuard kind expected = Admit.Guarded (groundingSource kind) expected (Grounding.operation kind)
    (λ token before after original present crash → registrationKeepsBinding token before after original
      (Grounding.interruptedKeepsRegistration kind token before after crash) present)

  module PropagationGuard expected = Admit.Guarded (Binding.advertised Tools.propagateFrom) expected Propagate.operation
    (λ token before after original present crash → registrationKeepsBinding token before after original
      (Propagate.interruptedKeepsRegistration token before after crash) present)
  module DecayGuard expected = Admit.Guarded (Binding.advertised Tools.decayAll) expected Decaying.operation
    (λ token before after original present crash → registrationKeepsBinding token before after original
      (Decaying.interruptedKeepsRegistration token before after crash) present)
  module ClearGuard expected = Admit.Guarded (Binding.advertised Tools.clearDocument) expected DocumentRemoval.operation
    (λ token before after original present crash → registrationKeepsBinding token before after original
      (DocumentRemoval.interruptedKeepsRegistration token before after crash) present)

  independentFirstBindings : ∀ metadata token before →
    Binding.bindings (proj₁ (IndependentWrite.first metadata token before)) ≡ Binding.bindings before
  independentFirstBindings metadata token before with IndependentWrite.firstClassification metadata token before
  ... | inj₁ same = cong Binding.bindings same
  ... | inj₂ (changed , reply , admitted , active , firstMissing , finalMissing , resultMissing , accepted) = trans
    (cong (λ outcome → Binding.bindings (proj₁ outcome))
      (IndependentWrite.freshPrefix metadata token before changed reply admitted active firstMissing finalMissing resultMissing accepted))
    (cong (λ registration → proj₁ (proj₂ (proj₂ registration)))
      (IndependentWrite.O.Saved.keepsRegistration metadata token before changed reply accepted))
  module IndependentFinalFrame observed = Binding.AdmittedStep ℕ IndependentWrite.B.Diagnostic (λ token → token)
    IndependentIntent.publicationKey Independent.publicationDistinct (IndependentWrite.decide observed)
    (IndependentWrite.journal observed) IndependentWrite.admit

  independentSecondBindings : ∀ observed token before →
    Binding.bindings (proj₁ (IndependentWrite.second observed token before)) ≡ Binding.bindings before
  independentSecondBindings observed token before with Store.lookupSaved before token (IndependentIntent.ownerKey token)
  ... | nothing = refl
  ... | just _ = IndependentFinalFrame.bindingsUnchanged observed token before

  independentAtomicBindings : ∀ before effect reply after → IndependentPublic.Atomic before effect reply after →
    Binding.bindings after ≡ Binding.bindings before
  independentAtomicBindings before (IndependentPublic.reserve token) (metadata , reply) after physical = trans
    (cong (λ outcome → Binding.bindings (proj₁ outcome))
      (IndependentWrite.Run.First.atomicObservation metadata token before after reply physical))
    (independentFirstBindings metadata token before)
  independentAtomicBindings before (IndependentPublic.readSources token) (inj₁ reason) after physical = cong Binding.bindings physical
  independentAtomicBindings before (IndependentPublic.readSources token) (inj₂ snapshot) after physical = cong Binding.bindings (proj₂ physical)
  independentAtomicBindings before (IndependentPublic.embed token cfg content) reply after physical = cong Binding.bindings physical
  independentAtomicBindings before (IndependentPublic.publish token observed) reply after physical = trans
    (cong (λ outcome → Binding.bindings (proj₁ outcome))
      (IndependentWrite.Run.Second.atomicObservation observed token before after reply physical))
    (independentSecondBindings observed token before)
  module IndependentFrame = BindingFrame IndependentPublic.Atomic independentAtomicBindings
  module IndependentGuard expected = Admit.Guarded (Binding.advertised Tools.insertBelief) expected
    (IndependentPublic.toRecoverable IndependentPublic.fullOperation)
    (λ token → IndependentFrame.existingBindingSurvives (IndependentPublic.script token) token)

  independentObserved : ∀ expected (proof : IndependentPublic.Operation) token before after response →
    IndependentGuard.X.Completed expected (IndependentGuard.script expected token) before after
      (IndependentGuard.executed response) →
    Data.Product.Σ (IndependentPublic.X.Completed (IndependentPublic.script token) before after response)
      (λ actual → IndependentPublic.X.Completed.events actual ≡ IndependentPublic.Result.transcript response)
  independentObserved expected proof token before after response complete =
    actual , IndependentPublic.Operation.observes proof token before after response actual
    where
    actual = proj₂ (IndependentGuard.completionMeaning expected token before after
      (IndependentGuard.executed response) complete)

  data Kind : Set where
    basic : Basic.Request → Kind
    experiences : Experiences.Request → Kind
    assessments : Assessments.Request → Kind
    intervention : Intervention.Input → Kind
    retrieval : Search.Request → Kind
    context : Context.Request → Kind
    documentQuery : Documents.Request → Kind
    projectRemoval : Text → Kind
    correction : Validation.Fault → Kind
    patternWrite patternRemoval beliefRemoval : Public.Request → Kind
    independentWrite : Public.Request → Kind
    propagation decay documentRemoval : Public.Request → Kind
    relationship : Edges.Kind → Public.Request → Kind
    grounding : Ground.Kind → Public.Request → Kind
    defeat sweep sourceWrite reviewWrite documentLoading : Public.Request → Kind
    control : (request : Controls.Request) → Controls.Input request → Kind

  Input : Kind → Set
  Input (basic _) = ⊤
  Input (experiences _) = ⊤
  Input (assessments _) = ⊤
  Input (intervention _) = ⊤
  Input (retrieval _) = ⊤
  Input (context _) = ⊤
  Input (documentQuery _) = ⊤
  Input (projectRemoval _) = ℕ
  Input (correction _) = ⊤
  Input (patternWrite _) = ℕ
  Input (independentWrite _) = ℕ
  Input (patternRemoval _) = ℕ
  Input (beliefRemoval _) = ℕ
  Input (relationship _ _) = ℕ
  Input (grounding _ _) = ℕ
  Input (propagation _) = ℕ
  Input (decay _) = ℕ
  Input (documentRemoval _) = ℕ
  Input (defeat _) = ℕ
  Input (sweep _) = ℕ
  Input (sourceWrite _) = ℕ
  Input (reviewWrite _) = ℕ
  Input (documentLoading _) = ℕ
  Input (control _ _) = ⊤

  Result : Kind → Set
  Result (basic _) = Wire.Value
  Result (experiences _) = Wire.Value
  Result (assessments _) = Assessments.Answer
  Result (intervention _) = Intervention.N.Result
  Result (retrieval _) = Retrieval.Result
  Result (context _) = LearningContext.Result
  Result (documentQuery _) = DocumentQuery.Result
  Result (projectRemoval _) = Wire.Value
  Result (correction _) = Validation.Fault
  Result (patternWrite expected) = PatternGuard.Result expected
  Result (independentWrite expected) = IndependentGuard.Result expected
  Result (patternRemoval expected) = PatternRemovalGuard.Result expected
  Result (beliefRemoval expected) = BeliefRemovalGuard.Result expected
  Result (relationship kind expected) = RelationshipGuard.Result kind expected
  Result (grounding kind expected) = GroundingGuard.Result kind expected
  Result (propagation expected) = PropagationGuard.Result expected
  Result (decay expected) = DecayGuard.Result expected
  Result (documentRemoval expected) = ClearGuard.Result expected
  Result (defeat _) = Defeating.Run.Value
  Result (sweep _) = Sweeping.Saved.Reply
  Result (sourceWrite _) = Recording.Saved.Reply
  Result (reviewWrite _) = Reviewing.Result
  Result (documentLoading _) = DocumentEntry.Outcome
  Result (control request _) = Control.Result request

  Goal : (kind : Kind) → Input kind → Store.World → Store.World → Result kind → Set
  Goal (basic request) = BasicFixed.Meaning request
  Goal (experiences request) = ExperienceFixed.Meaning request
  Goal (assessments request) = AssessmentFixed.Meaning request
  Goal (intervention request) = InterventionFixed.Meaning request
  Goal (retrieval request) = RetrievalFixed.Meaning request
  Goal (context request) = ContextFixed.Meaning request
  Goal (documentQuery request) = DocumentFixed.Meaning request
  Goal (projectRemoval project) = ProjectSelected.Meaning project
  Goal (correction diagnostic) = Refusal.Goal diagnostic
  Goal (patternWrite expected) = PatternGuard.Goal expected
  Goal (independentWrite expected) = IndependentGuard.Goal expected
  Goal (patternRemoval expected) = PatternRemovalGuard.Goal expected
  Goal (beliefRemoval expected) = BeliefRemovalGuard.Goal expected
  Goal (relationship kind expected) = RelationshipGuard.Goal kind expected
  Goal (grounding kind expected) = GroundingGuard.Goal kind expected
  Goal (propagation expected) = PropagationGuard.Goal expected
  Goal (decay expected) = DecayGuard.Goal expected
  Goal (documentRemoval expected) = ClearGuard.Goal expected
  Goal (defeat _) = Defeating.Goal
  Goal (sweep _) = Sweeping.Goal
  Goal (sourceWrite _) = Recording.Goal
  Goal (reviewWrite _) = Reviewing.Goal
  Goal (documentLoading _) = DocumentEntry.EntryGoal
  Goal (control request input) = ControlFixed.Meaning request input

  -- Observed operations require their complete certificate at assembly.
  -- There is no generic recoverability constructor for these cases.
  Certificate : Kind → Set₁
  Certificate (retrieval request) = Retrieval.Operation
  Certificate (context request) = LearningContext.Operation
  Certificate (documentQuery request) = DocumentQuery.Operation
  Certificate (independentWrite expected) = IndependentPublic.Operation
  Certificate (documentLoading expected) = DocumentEntry.Operation
  Certificate kind = Recovery.RecoverableFor Store.World (Input kind) (Result kind) (Goal kind)

  certificate : ReviewEnvironment → (kind : Kind) → Certificate kind
  certificate environment (basic request) = BasicFixed.operation request
  certificate environment (experiences request) = ExperienceFixed.operation request
  certificate environment (assessments request) = AssessmentFixed.operation request
  certificate environment (intervention request) = InterventionFixed.operation request
  certificate environment (retrieval request) = Retrieval.operation
  certificate environment (context request) = LearningContext.operation
  certificate environment (documentQuery request) = DocumentQuery.fullOperation
  certificate environment (projectRemoval project) = ProjectSelected.operation project
  certificate environment (correction diagnostic) = Refusal.operation diagnostic
  certificate environment (patternWrite expected) = PatternGuard.operation expected
  certificate environment (independentWrite expected) = IndependentPublic.fullOperation
  certificate environment (patternRemoval expected) = PatternRemovalGuard.operation expected
  certificate environment (beliefRemoval expected) = BeliefRemovalGuard.operation expected
  certificate environment (relationship kind expected) = RelationshipGuard.operation kind expected
  certificate environment (grounding kind expected) = GroundingGuard.operation kind expected
  certificate environment (propagation expected) = PropagationGuard.operation expected
  certificate environment (decay expected) = DecayGuard.operation expected
  certificate environment (documentRemoval expected) = ClearGuard.operation expected
  certificate environment (defeat expected) = Defeating.operation
  certificate environment (sweep expected) = Sweeping.operation
  certificate environment (sourceWrite expected) = Recording.operation
  certificate environment (reviewWrite expected) = Reviewing.operation environment
  certificate environment (documentLoading expected) = DocumentEntry.fullOperation
  certificate environment (control request input) = ControlFixed.operation request input

  executable : (kind : Kind) → Certificate kind →
    Recovery.RecoverableFor Store.World (Input kind) (Result kind) (Goal kind)
  executable (retrieval request) proof = Fixed.operation (Retrieval.toRecoverable proof) request
  executable (context request) proof = Fixed.operation (LearningContext.toRecoverable proof) request
  executable (documentQuery request) proof = Fixed.operation (DocumentQuery.toRecoverable proof) request
  executable (independentWrite expected) proof = IndependentGuard.operationWith expected
    (IndependentPublic.Operation.recovers proof) (IndependentPublic.Operation.progresses proof)
  executable (documentLoading expected) proof = DocumentEntry.toRecoverable proof
  executable (basic _) proof = proof
  executable (experiences _) proof = proof
  executable (assessments _) proof = proof
  executable (intervention _) proof = proof
  executable (projectRemoval _) proof = proof
  executable (correction _) proof = proof
  executable (patternWrite _) proof = proof
  executable (patternRemoval _) proof = proof
  executable (beliefRemoval _) proof = proof
  executable (relationship _ _) proof = proof
  executable (grounding _ _) proof = proof
  executable (propagation _) proof = proof
  executable (decay _) proof = proof
  executable (documentRemoval _) proof = proof
  executable (defeat _) proof = proof
  executable (sweep _) proof = proof
  executable (sourceWrite _) proof = proof
  executable (reviewWrite _) proof = proof
  executable (control _ _) proof = proof

  stepSucceeded : ∀ {Diagnostic : Set} → Step.Result Diagnostic → Set
  stepSucceeded (Step.done _) = ⊤
  stepSucceeded _ = ⊥

  querySucceeded : DocumentAnswer.Result → Set
  querySucceeded (DocumentAnswer.found _) = ⊤
  querySucceeded _ = ⊥

  -- Completion of a diagnostic is not completion of the requested write.
  -- Every success classification is fixed by this concrete reply family.
  Success : (kind : Kind) → Result kind → Set
  Success (basic _) _ = ⊤
  Success (experiences _) _ = ⊤
  Success (assessments _) reply = Σ Wire.Value (λ value → Assessments.successfulWire reply ≡ just value)
  Success (intervention _) reply = Intervention.Success reply
  Success (retrieval _) _ = ⊤
  Success (context _) (LearningContext.needsInput _ _) = ⊥
  Success (context _) (LearningContext.contextResult _ (LearningContext.Assembly.response _)) = ⊤
  Success (context _) (LearningContext.contextResult _ LearningContext.Assembly.invalidAssessment) = ⊥
  Success (documentQuery _) reply = querySucceeded (DocumentQuery.value reply)
  Success (projectRemoval _) reply = Σ ℕ (λ count → reply ≡
    Wire.object ((toList "deleted" , Wire.unsigned count) Data.List.∷ []))
  Success (correction _) _ = ⊥
  Success (patternWrite expected) (PatternGuard.needsInput _) = ⊥
  Success (patternWrite expected) (PatternGuard.executed reply) = stepSucceeded reply
  Success (independentWrite expected) (IndependentGuard.needsInput _) = ⊥
  Success (independentWrite expected) (IndependentGuard.executed reply) = stepSucceeded (IndependentPublic.Result.value reply)
  Success (patternRemoval expected) (PatternRemovalGuard.needsInput _) = ⊥
  Success (patternRemoval expected) (PatternRemovalGuard.executed reply) = stepSucceeded reply
  Success (beliefRemoval expected) (BeliefRemovalGuard.needsInput _) = ⊥
  Success (beliefRemoval expected) (BeliefRemovalGuard.executed reply) = stepSucceeded reply
  Success (relationship kind expected) (RelationshipGuard.needsInput _) = ⊥
  Success (relationship kind expected) (RelationshipGuard.executed reply) = stepSucceeded reply
  Success (grounding kind expected) (GroundingGuard.needsInput _) = ⊥
  Success (grounding kind expected) (GroundingGuard.executed reply) = stepSucceeded reply
  Success (propagation expected) (PropagationGuard.needsInput _) = ⊥
  Success (propagation expected) (PropagationGuard.executed reply) = stepSucceeded reply
  Success (decay expected) (DecayGuard.needsInput _) = ⊥
  Success (decay expected) (DecayGuard.executed reply) = stepSucceeded reply
  Success (documentRemoval expected) (ClearGuard.needsInput _) = ⊥
  Success (documentRemoval expected) (ClearGuard.executed reply) = stepSucceeded reply
  Success (defeat _) reply = stepSucceeded reply
  Success (sweep _) reply = stepSucceeded reply
  Success (sourceWrite _) reply = stepSucceeded reply
  Success (reviewWrite _) reply = stepSucceeded reply
  Success (documentLoading _) reply = stepSucceeded (DocumentEntry.normalized reply)
  Success (control Controls.readOutcome _) Control.Read.unknownToken = ⊥
  Success (control request _) reply = Control.Success request reply

  invalidPage : Validation.Fault
  invalidPage = Validation.fault (Validation.key "limit" Data.List.∷ []) Validation.invalidNumber
    "A page size must be positive. Supply the intended positive limit, or omit both limit and offset to return all matching beliefs. Do not use zero to mean all."
  invalidPendingSelection : Validation.Fault
  invalidPendingSelection = Validation.fault (Validation.key "limit" Data.List.∷ []) Validation.invalidNumber
    "The pending-experience selection must be positive when supplied. Supply the intended positive limit, or omit limit to return all matches. Do not use zero to mean all."

  graphRead : GraphRead.Request → Kind
  graphRead (GraphRead.getBelief identity) = basic (Basic.getBelief identity)
  graphRead (GraphRead.getPattern identity) = basic (Basic.getPattern identity)
  graphRead (GraphRead.listBeliefs project memory) = basic (Basic.listBeliefs project memory)
  graphRead (GraphRead.listPatterns project) = basic (Basic.listPatterns project)
  graphRead (GraphRead.beliefPage project memory zero offset) = correction invalidPage
  graphRead (GraphRead.beliefPage project memory (suc count) offset) = basic (Basic.beliefPage project memory count offset)
  graphRead (GraphRead.explain identity offset selection) = assessments (Assessments.explanation identity offset selection)
  graphRead GraphRead.stats = basic Basic.stats

  learningQuery : LearningQuery.Request → Kind
  learningQuery (LearningQuery.experience identity) = experiences (Experiences.experience identity)
  learningQuery (LearningQuery.currentReview identity) = experiences (Experiences.currentReview identity)
  learningQuery (LearningQuery.history identity) = experiences (Experiences.history identity)
  learningQuery (LearningQuery.pending project nothing excluded) = experiences (Experiences.pending project nothing excluded)
  learningQuery (LearningQuery.pending project (just zero) excluded) = correction invalidPendingSelection
  learningQuery (LearningQuery.pending project (just (suc count)) excluded) = experiences
    (Experiences.pending project (just (Ranking.positiveCount (suc count) (s≤s z≤n))) excluded)
  learningQuery (LearningQuery.score selection) = assessments (Assessments.scores selection)
  learningQuery (LearningQuery.assessmentHistory selection offset count) = assessments (Assessments.history selection offset count)

  perCallRetention : Validation.Fault
  perCallRetention = Validation.fault (Validation.key "grace_hours" Data.List.∷ []) Validation.unknownField
    "Retention is chosen by the user in retirement.grace_hours, not by an operation argument. Remove the per-call override and use the configured sweep request. If that policy is missing, ask the user to choose it."

  -- This is the closed semantic request table. It determines the concrete
  -- business certificate; raw invocation/binding admission is assembled before
  -- writable bodies, never replaced by selecting a different goal or script.
  classify : Public.Request → Kind
  classify expected@(Public.mutation (Mutation.belief content probability confidence project memory provenance citations)) = independentWrite expected
  classify expected@(Public.mutation (Mutation.patternNode situation approach success project)) = patternWrite expected
  classify expected@(Public.mutation (Mutation.edge from to Relations.supports weight)) = relationship Edges.support expected
  classify expected@(Public.mutation (Mutation.edge from to Relations.causes weight)) = relationship Edges.cause expected
  classify expected@(Public.mutation (Mutation.edge from to Relations.contradicts weight)) = relationship Edges.contradiction expected
  classify expected@(Public.mutation (Mutation.edge from to Relations.defeats weight)) = defeat expected
  classify (Public.read request) = graphRead request
  classify expected@(Public.delete Deletion.belief identity) = beliefRemoval expected
  classify expected@(Public.delete Deletion.patternNode identity) = patternRemoval expected
  classify (Public.deleteProject project) = projectRemoval project
  classify expected@(Public.inference (InferenceRequest.propagate identity)) = propagation expected
  classify (Public.inference (InferenceRequest.intervention identity value)) = intervention (Intervention.input identity value)
  classify expected@(Public.inference (InferenceRequest.decay project factor)) = decay expected
  classify (Public.inference (InferenceRequest.contradictions project)) = basic (Basic.contradictions project)
  classify (Public.inference (InferenceRequest.sweep project threshold grace)) = correction perCallRetention
  classify expected@(Public.sweepConfigured project threshold) = sweep expected
  classify (Public.relevant queryText selection project preference includeEvidence perBelief) = retrieval
    (Search.fromFields queryText selection project preference includeEvidence perBelief)
  classify expected@(Public.addEvidence belief chunk weight) = grounding Ground.addition expected
  classify expected@(Public.removeEvidence belief chunk) = grounding Ground.removal expected
  classify (Public.evidence belief) = basic (Basic.evidence belief)
  classify expected@(Public.loadDocument path project) = documentLoading expected
  classify (Public.queryDocument queryText project selection) = documentQuery (Documents.query queryText project selection)
  classify expected@(Public.clearDocument path) = documentRemoval expected
  classify expected@(Public.learning (Learning.recordExperience source revision)) = sourceWrite expected
  classify expected@(Public.learning (Learning.reviewExperience review revision)) = reviewWrite expected
  classify (Public.learningQuery request) = learningQuery request
  classify (Public.learningContext queryText project selection) = context (Context.contextSearch queryText project selection)
  classify Public.capabilities = basic Basic.capabilities
  classify (Public.reserveOperation requestKey) = control Controls.reserve requestKey
  classify (Public.operationOutcome token) = control Controls.readOutcome token
  classify (Public.cancelOperation token) = control Controls.cancel token

  operation : (environment : ReviewEnvironment) → (request : Public.Request) → Certificate (classify request)
  operation environment request = certificate environment (classify request)

  data ReadRequest : Set where
    graphCall : GraphRead.Request → ReadRequest
    relevantCall : Search.Request → ReadRequest
    evidenceCall : ℕ → ReadRequest
    documentCall : Documents.Request → ReadRequest

  readKind : ReadRequest → Kind
  readKind (graphCall request) = graphRead request
  readKind (relevantCall request) = retrieval request
  readKind (evidenceCall identity) = basic (Basic.evidence identity)
  readKind (documentCall request) = documentQuery request

  data Call : Set where
    toolCall : Tools.Tool → Wire.Value → Call
    privateRead : ReadRequest → Call

  record Choice : Set where
    constructor choose
    field kind : Kind; input : Input kind

  missingToken : Validation.Fault
  missingToken = Validation.fault (Validation.key "operation_token" Data.List.∷ []) Validation.missingField
    "This write requires its PostgreSQL-issued operation token. Reserve the request with a stable request_key and reuse that token for the same arguments; read its outcome if a reply was lost."
  withToken : (ℕ → Choice) → Data.Maybe.Maybe ℕ → Choice
  withToken ready (just token) = ready token
  withToken ready nothing = choose (correction missingToken) tt

  chooseInput : Kind → Data.Maybe.Maybe ℕ → Choice
  chooseInput kind@(basic _) _ = choose kind tt
  chooseInput kind@(experiences _) _ = choose kind tt
  chooseInput kind@(assessments _) _ = choose kind tt
  chooseInput kind@(intervention _) _ = choose kind tt
  chooseInput kind@(retrieval _) _ = choose kind tt
  chooseInput kind@(context _) _ = choose kind tt
  chooseInput kind@(documentQuery _) _ = choose kind tt
  chooseInput kind@(correction _) _ = choose kind tt
  chooseInput kind@(control _ _) _ = choose kind tt
  chooseInput kind@(projectRemoval _) token = withToken (choose kind) token
  chooseInput kind@(patternWrite _) token = withToken (choose kind) token
  chooseInput kind@(independentWrite _) token = withToken (choose kind) token
  chooseInput kind@(patternRemoval _) token = withToken (choose kind) token
  chooseInput kind@(beliefRemoval _) token = withToken (choose kind) token
  chooseInput kind@(relationship _ _) token = withToken (choose kind) token
  chooseInput kind@(grounding _ _) token = withToken (choose kind) token
  chooseInput kind@(propagation _) token = withToken (choose kind) token
  chooseInput kind@(decay _) token = withToken (choose kind) token
  chooseInput kind@(documentRemoval _) token = withToken (choose kind) token
  chooseInput kind@(defeat _) token = withToken (choose kind) token
  chooseInput kind@(sweep _) token = withToken (choose kind) token
  chooseInput kind@(sourceWrite _) token = withToken (choose kind) token
  chooseInput kind@(reviewWrite _) token = withToken (choose kind) token
  chooseInput kind@(documentLoading _) token = withToken (choose kind) token

  tokenForKind : (kind : Tools.Kind) → Public.TokenForKind kind → Data.Maybe.Maybe ℕ
  tokenForKind Tools.businessWrite token = just token
  tokenForKind Tools.readOnly tt = nothing
  tokenForKind Tools.operationControl tt = nothing

  resolve : Call → Choice
  resolve (toolCall tool submitted) with Request.readInvocation tool submitted
  ... | inj₁ fault = choose (correction fault) tt
  ... | inj₂ invocation = chooseInput (classify (Request.Invocation.request invocation))
    (tokenForKind (Tools.kind tool) (Request.Invocation.operationToken invocation))
  resolve (privateRead request) = chooseInput (readKind request) nothing

  selectedCertificate : ReviewEnvironment → (call : Call) → Certificate (Choice.kind (resolve call))
  selectedCertificate environment call = certificate environment (Choice.kind (resolve call))
  selectedOperation : (environment : ReviewEnvironment) → (call : Call) →
    Recovery.RecoverableFor Store.World (Input (Choice.kind (resolve call)))
      (Result (Choice.kind (resolve call))) (Goal (Choice.kind (resolve call)))
  selectedOperation environment call = executable (Choice.kind (resolve call)) (selectedCertificate environment call)


  module Creating = Binding.Creating library postgres using
    (Request; Call; Context; Result; needsInput; returned; ready; readProject; Environment
    ; Effect; Reply; Atomic; module X; module E; module Read; script; progress; Goal
    ; ReadyMeaning; completedReady; completedReadyResultAbsent; completedReadyReservation
    ; completedDecodedExistingUnchanged; readyRetrySameContext; transportReady; readyOperation
    ; matchesOriginalSettings)

  -- The closed native tool selects its concrete writer family. The caller
  -- supplies no family, input conversion, operation name or proof capability.
  module WriterSelection (environment : ReviewEnvironment) where
    module Replay = Cached environment
    record Selected (tool : Tools.Tool) : Set where
      field kind : Kind
            writer : Replay.Writer kind
            operationName : Replay.writerName writer ≡ toList (Tools.wireName tool)

    select : ∀ tool → Tools.kind tool ≡ Tools.businessWrite →
      ∀ {submitted} → Request.Invocation tool submitted → Selected tool
    select Tools.insertBelief allowed invocation = record
      { kind = independentWrite requested; writer = Replay.independentWriter; operationName = refl }
      where requested = Request.Invocation.request invocation
    select Tools.deleteBelief allowed invocation = record
      { kind = beliefRemoval requested; writer = Replay.beliefRemover; operationName = refl }
      where requested = Request.Invocation.request invocation
    select Tools.deleteProject allowed invocation = record
      { kind = projectRemoval (proj₁ project); writer = Replay.projectWriter; operationName = refl }
      where project = Creating.readProject (Request.Invocation.arguments invocation) (Request.Invocation.request invocation)
              (Request.Invocation.decoded invocation)
    select Tools.deletePattern allowed invocation = record
      { kind = patternRemoval requested; writer = Replay.patternRemover; operationName = refl }
      where requested = Request.Invocation.request invocation
    select Tools.insertPattern allowed invocation = record
      { kind = patternWrite requested; writer = Replay.patternWriter; operationName = refl }
      where requested = Request.Invocation.request invocation
    select Tools.recordSupport allowed invocation = record
      { kind = relationship Edges.support requested; writer = Replay.relationshipWriter; operationName = refl }
      where requested = Request.Invocation.request invocation
    select Tools.recordCause allowed invocation = record
      { kind = relationship Edges.cause requested; writer = Replay.relationshipWriter; operationName = refl }
      where requested = Request.Invocation.request invocation
    select Tools.recordDefeat allowed invocation = record
      { kind = defeat requested; writer = Replay.defeater; operationName = refl }
      where requested = Request.Invocation.request invocation
    select Tools.recordContradiction allowed invocation = record
      { kind = relationship Edges.contradiction requested; writer = Replay.relationshipWriter; operationName = refl }
      where requested = Request.Invocation.request invocation
    select Tools.getBelief () invocation
    select Tools.listBeliefs () invocation
    select Tools.listPatterns () invocation
    select Tools.getContradictions () invocation
    select Tools.decayAll allowed invocation = record
      { kind = decay requested; writer = Replay.decayer; operationName = refl }
      where requested = Request.Invocation.request invocation
    select Tools.sweepExpiredDefeated allowed invocation = record
      { kind = sweep requested; writer = Replay.sweeper; operationName = refl }
      where requested = Request.Invocation.request invocation
    select Tools.queryRelevant () invocation
    select Tools.addEvidence allowed invocation = record
      { kind = grounding Ground.addition requested; writer = Replay.groundingWriter; operationName = refl }
      where requested = Request.Invocation.request invocation
    select Tools.getEvidence () invocation
    select Tools.propagateFrom allowed invocation = record
      { kind = propagation requested; writer = Replay.propagator; operationName = refl }
      where requested = Request.Invocation.request invocation
    select Tools.queryIntervention () invocation
    select Tools.loadDocument allowed invocation = record
      { kind = documentLoading requested; writer = Replay.documentLoader; operationName = refl }
      where requested = Request.Invocation.request invocation
    select Tools.queryDocument () invocation
    select Tools.clearDocument allowed invocation = record
      { kind = documentRemoval requested; writer = Replay.documentRemover; operationName = refl }
      where requested = Request.Invocation.request invocation
    select Tools.getLearningReview () invocation
    select Tools.learningCapabilities () invocation
    select Tools.getLessonAssessment () invocation
    select Tools.lessonAssessmentHistory () invocation
    select Tools.explainBelief () invocation
    select Tools.recordExperience allowed invocation = record
      { kind = sourceWrite requested; writer = Replay.sourceWriter; operationName = refl }
      where requested = Request.Invocation.request invocation
    select Tools.pendingExperiences () invocation
    select Tools.reviewExperience allowed invocation = record
      { kind = reviewWrite requested; writer = Replay.reviewer; operationName = refl }
      where requested = Request.Invocation.request invocation
    select Tools.getExperience () invocation
    select Tools.experienceHistory () invocation
    select Tools.queryLearningContext () invocation
    select Tools.reserveOperation () invocation
    select Tools.operationOutcome () invocation
    select Tools.cancelOperation () invocation

    selected : (call : Creating.Call) → Selected (Creating.Call.tool call)
    selected call = select (Creating.Call.tool call) (Creating.Call.writer call) (Creating.Call.invocation call)
    choice : Creating.Call → Choice
    choice call = choose (Selected.kind (selected call))
      (Replay.writerInput (Selected.writer (selected call)) (Creating.Call.token call))

  -- The creating prefix is assembled here with the fixed concrete body.
  -- Neither an operation nor its business goal is a public request field.
  module PublicWrites (environment : ReviewEnvironment) (preparation : Creating.Environment) where
    module Selection = WriterSelection environment
    module Replay = Cached environment
    choice : Creating.Context → Choice
    choice scope = Selection.choice (Creating.Context.call scope)
    bodyKind : Creating.Context → Kind
    bodyKind scope = Choice.kind (choice scope)
    bodyInput : (scope : Creating.Context) → Input (bodyKind scope)
    bodyInput scope = Choice.input (choice scope)
    bodyWriter : (scope : Creating.Context) → Replay.Writer (bodyKind scope)
    bodyWriter scope = Selection.Selected.writer (Selection.selected (Creating.Context.call scope))
    bodyName : ∀ scope → Replay.writerName (bodyWriter scope) ≡ Creating.Call.name (Creating.Context.call scope)
    bodyName scope = Selection.Selected.operationName (Selection.selected (Creating.Context.call scope))
    bodyCertificate : (scope : Creating.Context) → Certificate (bodyKind scope)
    bodyCertificate scope = certificate environment (bodyKind scope)
    bodyOperation : (scope : Creating.Context) → Recovery.RecoverableFor Store.World
      (Input (bodyKind scope)) (Result (bodyKind scope)) (Goal (bodyKind scope))
    bodyOperation scope = executable (bodyKind scope) (bodyCertificate scope)
    module Body (scope : Creating.Context) = Recovery.RecoverableFor (bodyOperation scope)
      using (Effect; Reply; Atomic; module X; module E; script; progress; completedMeetsGoal; converges)

    data Response : Set where
      needsInput : Validation.Fault → Response
      returned : Creating.Read.Result → Response
      executed : (scope : Creating.Context) → Result (bodyKind scope) → Response

    data Effect : Set where
      prepare : Creating.Effect → Effect
      publish : (scope : Creating.Context) → Body.Effect scope → Effect
    Reply : Effect → Set
    Reply (prepare effect) = Creating.Reply effect
    Reply (publish scope effect) = Body.Reply scope effect
    Atomic : Store.World → (effect : Effect) → Reply effect → Store.World → Set
    Atomic before (prepare effect) reply after = Creating.Atomic before effect reply after
    Atomic before (publish scope effect) reply after = Body.Atomic scope before effect reply after
    module X = Recovery.Execution Store.World Effect Reply Atomic
    module E = X.E

    liftPrefix : ∀ {R} → Creating.E.Script R → E.Script R
    liftPrefix (Creating.E.done reply) = E.done reply
    liftPrefix (Creating.E.ask effect next) = E.ask (prepare effect) (λ reply → liftPrefix (next reply))
    liftBody : ∀ scope → Body.E.Script scope (Result (bodyKind scope)) → E.Script Response
    liftBody scope (Body.E.done reply) = E.done (executed scope reply)
    liftBody scope (Body.E.ask effect next) = E.ask (publish scope effect) (λ reply → liftBody scope (next reply))
    afterPreparation : Creating.Result → E.Script Response
    afterPreparation (Creating.needsInput fault) = E.done (needsInput fault)
    afterPreparation (Creating.returned outcome) = E.done (returned outcome)
    afterPreparation (Creating.ready scope) = liftBody scope (Body.script scope (bodyInput scope))
    script : Creating.Request → E.Script Response
    script requested = E._>>=_ (liftPrefix (Creating.script requested)) afterPreparation

    prefixEvent : Creating.E.Event → E.Event
    prefixEvent (effect , reply) = prepare effect , reply
    bodyEvent : ∀ scope → Body.E.Event scope → E.Event
    bodyEvent scope (effect , reply) = publish scope effect , reply
    prefixRuns : ∀ {R} {program : Creating.E.Script R} {events reply} →
      Creating.E.Runs program events reply → E.Runs (liftPrefix program) (Data.List.map prefixEvent events) reply
    prefixRuns (Creating.E.returned reply) = E.returned reply
    prefixRuns (Creating.E.replied effect next reply later) =
      E.replied (prepare effect) (λ observed → liftPrefix (next observed)) reply (prefixRuns later)
    bodyRuns : ∀ scope {program : Body.E.Script scope (Result (bodyKind scope))} {events reply} →
      Body.E.Runs scope program events reply →
      E.Runs (liftBody scope program) (Data.List.map (bodyEvent scope) events) (executed scope reply)
    bodyRuns scope (Body.E.returned reply) = E.returned (executed scope reply)
    bodyRuns scope (Body.E.replied effect next reply later) =
      E.replied (publish scope effect) (λ observed → liftBody scope (next observed)) reply (bodyRuns scope later)
    prefixChanges : ∀ {before events after} → Creating.X.Changes before events after →
      X.Changes before (Data.List.map prefixEvent events) after
    prefixChanges (Creating.X.unchanged before) = X.unchanged before
    prefixChanges (Creating.X.changed before effect reply middle physical later) =
      X.changed before (prepare effect) reply middle physical (prefixChanges later)
    bodyChanges : ∀ scope {before events after} → Body.X.Changes scope before events after →
      X.Changes before (Data.List.map (bodyEvent scope) events) after
    bodyChanges scope (Body.X.unchanged before) = X.unchanged before
    bodyChanges scope (Body.X.changed before effect reply middle physical later) =
      X.changed before (publish scope effect) reply middle physical (bodyChanges scope later)

    afterPreparationProgress : ∀ prepared before → Σ Store.World (λ after → Σ Response
      (λ reply → X.Completed (afterPreparation prepared) before after reply))
    afterPreparationProgress (Creating.needsInput fault) before =
      before , needsInput fault , X.completed [] (E.returned _) (X.unchanged before)
    afterPreparationProgress (Creating.returned outcome) before =
      before , returned outcome , X.completed [] (E.returned _) (X.unchanged before)
    afterPreparationProgress (Creating.ready scope) before with Body.progress scope (bodyInput scope) before
    ... | after , reply , Body.X.completed events execution changes = after , executed scope reply ,
      X.completed (Data.List.map (bodyEvent scope) events) (bodyRuns scope execution) (bodyChanges scope changes)
    progress : ∀ requested before → Σ Store.World (λ after → Σ Response
      (λ reply → X.Completed (script requested) before after reply))
    progress requested before with Creating.progress preparation requested before
    ... | middle , prepared , Creating.X.completed prefixEvents prefixExecution prefixPhysical
      with afterPreparationProgress prepared middle
    ... | after , reply , X.completed bodyEvents bodyExecution bodyPhysical = after , reply , X.completed _
      (E.bindRuns (prefixRuns prefixExecution) bodyExecution) (X.changesAppend (prefixChanges prefixPhysical) bodyPhysical)

    -- Prefix-only outcomes preserve the whole business World. A body result
    -- owes its independently specified business outcome from the original
    -- prepared baseline, including on a retry after any committed boundary.
    data Meaning (requested : Creating.Request) (before after : Store.World) : Response → Set where
      preparationDialogue : ∀ fault → Creating.Goal requested before after (Creating.needsInput fault) →
        Meaning requested before after (needsInput fault)
      preparationReadback : ∀ outcome → Creating.Goal requested before after (Creating.returned outcome) →
        Meaning requested before after (returned outcome)
      businessOutcome : ∀ baseline scope reply →
        Creating.Goal requested before baseline (Creating.ready scope) →
        Goal (bodyKind scope) (bodyInput scope) baseline after reply →
        Meaning requested before after (executed scope reply)
      cachedBusinessOutcome : ∀ baseline scope reply original raw →
        Creating.Goal requested before baseline (Creating.ready scope) →
        Goal (bodyKind scope) (bodyInput scope) baseline after reply →
        Replay.savedValue (bodyWriter scope) reply ≡ just raw →
        Creating.Read.answer (Creating.Call.token (Creating.Context.call scope)) after ≡ Creating.Read.completed original raw →
        Meaning requested before after (returned (Creating.Read.completed original raw))

    splitPrefixRun : ∀ (program : Creating.E.Script Creating.Result) before after reply {events} →
      E.Runs (E._>>=_ (liftPrefix program) afterPreparation) events reply → X.Changes before events after →
      Σ Store.World (λ middle → Σ Creating.Result (λ prepared →
        Creating.X.Completed program before middle prepared × X.Completed (afterPreparation prepared) middle after reply))
    splitPrefixRun (Creating.E.done prepared) before after reply execution changes = before , prepared ,
      Creating.X.completed [] (Creating.E.returned prepared) (Creating.X.unchanged before) , X.completed _ execution changes
    splitPrefixRun (Creating.E.ask effect next) before after reply
      (E.replied .(prepare effect) _ observed execution)
      (X.changed .before .(prepare effect) .observed middle physical changes)
      with splitPrefixRun (next observed) middle after reply execution changes
    ... | baseline , prepared , Creating.X.completed events prefixExecution prefixPhysical , completedBody =
      baseline , prepared , Creating.X.completed ((effect , observed) Data.List.∷ events)
        (Creating.E.replied effect next observed prefixExecution)
        (Creating.X.changed before effect observed middle physical prefixPhysical) , completedBody

    unliftBodyRun : ∀ scope (program : Body.E.Script scope (Result (bodyKind scope))) before after reply {events} →
      E.Runs (liftBody scope program) events reply → X.Changes before events after →
      Σ (Result (bodyKind scope)) (λ actual → reply ≡ executed scope actual × Body.X.Completed scope program before after actual)
    unliftBodyRun scope (Body.E.done actual) before .before .(executed scope actual)
      (E.returned _) (X.unchanged _) = actual , refl , Body.X.completed [] (Body.E.returned actual) (Body.X.unchanged before)
    unliftBodyRun scope (Body.E.ask effect next) before after reply
      (E.replied .(publish scope effect) _ observed execution)
      (X.changed .before .(publish scope effect) .observed middle physical changes)
      with unliftBodyRun scope (next observed) middle after reply execution changes
    ... | actual , same , Body.X.completed events bodyExecution bodyPhysical = actual , same ,
      Body.X.completed ((effect , observed) Data.List.∷ events) (Body.E.replied effect next observed bodyExecution)
        (Body.X.changed before effect observed middle physical bodyPhysical)

    prependPrefixInterruption : ∀ before effect (continuation : Creating.Reply effect → Creating.E.Script Creating.Result) reply middle after →
      Creating.Atomic before effect reply middle → Creating.X.Interrupted (continuation reply) middle after →
      Creating.X.Interrupted (Creating.E.ask effect continuation) before after
    prependPrefixInterruption before effect continuation reply middle after physical
      (Creating.X.atPrefix events residual .after prefix changes) =
      Creating.X.atPrefix ((effect , reply) ∷ events) residual after (Creating.E.replied effect continuation reply prefix)
        (Creating.X.changed before effect reply middle physical changes)
    prependPrefixInterruption before effect continuation reply middle after physical
      (Creating.X.beforeReply events active next current observed .after prefix changes activePhysical) =
      Creating.X.beforeReply ((effect , reply) ∷ events) active next current observed after
        (Creating.E.replied effect continuation reply prefix) (Creating.X.changed before effect reply middle physical changes) activePhysical

    prependBodyInterruption : ∀ scope before effect (continuation : Body.Reply scope effect → Body.E.Script scope (Result (bodyKind scope))) reply middle after →
      Body.Atomic scope before effect reply middle → Body.X.Interrupted scope (continuation reply) middle after →
      Body.X.Interrupted scope (Body.E.ask effect continuation) before after
    prependBodyInterruption scope before effect continuation reply middle after physical
      (Body.X.atPrefix events residual .after prefix changes) =
      Body.X.atPrefix ((effect , reply) ∷ events) residual after (Body.E.replied effect continuation reply prefix)
        (Body.X.changed before effect reply middle physical changes)
    prependBodyInterruption scope before effect continuation reply middle after physical
      (Body.X.beforeReply events active next current observed .after prefix changes activePhysical) =
      Body.X.beforeReply ((effect , reply) ∷ events) active next current observed after
        (Body.E.replied effect continuation reply prefix) (Body.X.changed before effect reply middle physical changes) activePhysical

    doneInterruptedSameWorld : ∀ (value : Response) before after → X.Interrupted (E.done value) before after → after ≡ before
    doneInterruptedSameWorld value before .before
      (X.atPrefix .[] .(E.done value) .before (E.stopped _) (X.unchanged .before)) = refl
    doneInterruptedSameWorld value before after (X.beforeReply events effect continuation current reply .after () changes physical)

    unliftBodyInterrupted : ∀ scope (program : Body.E.Script scope (Result (bodyKind scope))) before after →
      X.Interrupted (liftBody scope program) before after → Body.X.Interrupted scope program before after
    unliftBodyInterrupted scope (Body.E.done value) before after interrupted
      rewrite doneInterruptedSameWorld (executed scope value) before after interrupted =
      Body.X.atPrefix [] (Body.E.done value) before (Body.E.stopped _) (Body.X.unchanged before)
    unliftBodyInterrupted scope (Body.E.ask effect continuation) before .before
      (X.atPrefix .[] ._ .before (E.stopped _) (X.unchanged .before)) =
      Body.X.atPrefix [] (Body.E.ask effect continuation) before (Body.E.stopped _) (Body.X.unchanged before)
    unliftBodyInterrupted scope (Body.E.ask effect continuation) before after
      (X.atPrefix ._ residual .after (E.replied .(publish scope effect) _ reply prefix)
        (X.changed .before .(publish scope effect) .reply middle physical changes)) =
      prependBodyInterruption scope before effect continuation reply middle after physical
        (unliftBodyInterrupted scope (continuation reply) middle after (X.atPrefix _ residual after prefix changes))
    unliftBodyInterrupted scope (Body.E.ask effect continuation) before after
      (X.beforeReply .[] .(publish scope effect) ._ .before reply .after (E.stopped _) (X.unchanged .before) physical) =
      Body.X.beforeReply [] effect continuation before reply after (Body.E.stopped _) (Body.X.unchanged before) physical
    unliftBodyInterrupted scope (Body.E.ask effect continuation) before after
      (X.beforeReply ._ active next current observed .after (E.replied .(publish scope effect) _ reply prefix)
        (X.changed .before .(publish scope effect) .reply middle physical changes) activePhysical) =
      prependBodyInterruption scope before effect continuation reply middle after physical
        (unliftBodyInterrupted scope (continuation reply) middle after
          (X.beforeReply _ active next current observed after prefix changes activePhysical))

    data InterruptedPhase (program : Creating.E.Script Creating.Result) (before after : Store.World) : Set where
      preparing : Creating.X.Interrupted program before after → InterruptedPhase program before after
      publishing : ∀ baseline scope → Creating.X.Completed program before baseline (Creating.ready scope) →
        Body.X.Interrupted scope (Body.script scope (bodyInput scope)) baseline after → InterruptedPhase program before after

    prependPhase : ∀ before effect continuation reply middle after → Creating.Atomic before effect reply middle →
      InterruptedPhase (continuation reply) middle after → InterruptedPhase (Creating.E.ask effect continuation) before after
    prependPhase before effect continuation reply middle after physical (preparing interrupted) =
      preparing (prependPrefixInterruption before effect continuation reply middle after physical interrupted)
    prependPhase before effect continuation reply middle after physical
      (publishing baseline scope (Creating.X.completed events execution changes) interrupted) =
      publishing baseline scope (Creating.X.completed ((effect , reply) ∷ events)
        (Creating.E.replied effect continuation reply execution) (Creating.X.changed before effect reply middle physical changes)) interrupted

    splitInterruptedPrefix : ∀ (program : Creating.E.Script Creating.Result) before after →
      X.Interrupted (E._>>=_ (liftPrefix program) afterPreparation) before after → InterruptedPhase program before after
    splitInterruptedPrefix (Creating.E.done (Creating.ready scope)) before after interrupted =
      publishing before scope (Creating.X.completed [] (Creating.E.returned (Creating.ready scope)) (Creating.X.unchanged before))
        (unliftBodyInterrupted scope (Body.script scope (bodyInput scope)) before after interrupted)
    splitInterruptedPrefix (Creating.E.done (Creating.needsInput fault)) before after interrupted
      rewrite doneInterruptedSameWorld (needsInput fault) before after interrupted =
      preparing (Creating.X.atPrefix [] (Creating.E.done (Creating.needsInput fault)) before (Creating.E.stopped _) (Creating.X.unchanged before))
    splitInterruptedPrefix (Creating.E.done (Creating.returned outcome)) before after interrupted
      rewrite doneInterruptedSameWorld (returned outcome) before after interrupted =
      preparing (Creating.X.atPrefix [] (Creating.E.done (Creating.returned outcome)) before (Creating.E.stopped _) (Creating.X.unchanged before))
    splitInterruptedPrefix (Creating.E.ask effect continuation) before .before
      (X.atPrefix .[] ._ .before (E.stopped _) (X.unchanged .before)) =
      preparing (Creating.X.atPrefix [] (Creating.E.ask effect continuation) before (Creating.E.stopped _) (Creating.X.unchanged before))
    splitInterruptedPrefix (Creating.E.ask effect continuation) before after
      (X.atPrefix ._ residual .after (E.replied .(prepare effect) _ reply prefix)
        (X.changed .before .(prepare effect) .reply middle physical changes)) =
      prependPhase before effect continuation reply middle after physical
        (splitInterruptedPrefix (continuation reply) middle after (X.atPrefix _ residual after prefix changes))
    splitInterruptedPrefix (Creating.E.ask effect continuation) before after
      (X.beforeReply .[] .(prepare effect) ._ .before reply .after (E.stopped _) (X.unchanged .before) physical) =
      preparing (Creating.X.beforeReply [] effect continuation before reply after (Creating.E.stopped _) (Creating.X.unchanged before) physical)
    splitInterruptedPrefix (Creating.E.ask effect continuation) before after
      (X.beforeReply ._ active next current observed .after (E.replied .(prepare effect) _ reply prefix)
        (X.changed .before .(prepare effect) .reply middle physical changes) activePhysical) =
      prependPhase before effect continuation reply middle after physical
        (splitInterruptedPrefix (continuation reply) middle after
          (X.beforeReply _ active next current observed after prefix changes activePhysical))

    prefixThenBodyMeaning : ∀ requested before baseline after prepared reply →
      Creating.Goal requested before baseline prepared → X.Completed (afterPreparation prepared) baseline after reply →
      Meaning requested before after reply
    prefixThenBodyMeaning requested before baseline .baseline (Creating.needsInput fault) .(needsInput fault) certified
      (X.completed [] (E.returned _) (X.unchanged _)) = preparationDialogue fault certified
    prefixThenBodyMeaning requested before baseline .baseline (Creating.returned outcome) .(returned outcome) certified
      (X.completed [] (E.returned _) (X.unchanged _)) = preparationReadback outcome certified
    prefixThenBodyMeaning requested before baseline after (Creating.ready scope) reply certified
      (X.completed events execution changes)
      with unliftBodyRun scope (Body.script scope (bodyInput scope)) baseline after reply execution changes
    ... | actual , refl , completedBody = businessOutcome baseline scope actual certified
      (Body.completedMeetsGoal scope (bodyInput scope) baseline after actual completedBody)
