{-# OPTIONS --safe #-}
-- Concrete operation kinds determine their inputs, replies and business
-- goals. There is no caller-selected goal, script or physical relation here.
module Mimir.PublicOperationCatalogue where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Float.Base using (Float)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_)
import Data.Maybe
open import Data.Nat using (ℕ; zero; suc; s≤s; z≤n)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
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
import Mimir.RegisteredStoreAdmission as Registered
import Data.Maybe.Properties as Maybes
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
    using (Result; completed; Operation; operation; toRecoverable)
  module LearningContext = Context.Run arithmetic unicode vectors configuration textBefore
  module DocumentQuery = Documents.Run vectors configuration
    using (Result; value; Operation; fullOperation; toRecoverable)
  module PatternWrite = Pattern.Registered library format
    using (Internal; descriptor; key; distinct; decide; keepsJournal; admit; module X; script; interruptionState; operation; cachedReplay)
  module PatternRemoval = DeletePattern.Registered library
    using (descriptor; key; distinct; decide; keepsJournal; admit; operation; cachedReplay)
  module Relationship kind = Edges.Registered library kind
    using (key; distinct; decide; keepsJournal; admit; operation; cachedReplay)
  module BeliefRemoval = DeleteBelief.Registered library databaseSum calculator serverTime
    using (module X; script; Internal; descriptor; key; distinct; decide; keepsJournal; admit; interruptionState; operation; interruptedKeepsRegistration; interruptedKeepsCancellation; cachedReplay)
  module Grounding kind = Ground.Registered kind library databaseSum calculator serverTime
    using (module X; script; Internal; descriptor; key; distinct; decide; keepsJournal; admit; interruptionState; operation; interruptedKeepsRegistration; interruptedKeepsCancellation; cachedReplay)
  module Propagate = Propagation.Registered format library databaseSum calculator serverTime
    using (module X; script; Internal; descriptor; key; distinct; decide; keepsJournal; admit; interruptionState; operation; interruptedKeepsRegistration; interruptedKeepsCancellation; cachedReplay)
  module Decaying = Decay.Registered library databaseSum serverTime
    using (module X; script; Internal; descriptor; key; distinct; decide; keepsJournal; admit; interruptionState; operation; interruptedKeepsRegistration; interruptedKeepsCancellation; cachedReplay)
  module DocumentRemoval = Clear.Registered library databaseSum calculator serverTime
    using (module X; script; Internal; descriptor; key; distinct; decide; keepsJournal; admit; interruptionState; operation; interruptedKeepsRegistration; interruptedKeepsCancellation; cachedReplay)
  module IndependentWrite = Independent.Registered format library databaseSum calculator allocateOwner
  module IndependentPublic = IndependentWrite.Public configuration
  module Defeating = Defeat.Registered library databaseSum calculator serverTime
    using (Value; Goal; operation; cachedReplay)
  module Sweeping = Sweep.Registered library format databaseSum calculator sweepObservation
    using (Result; Goal; operation; cachedReplay)
  module Recording = Source.Registered library format database databaseSum calculator sourcePostgres
    using (Result; Goal; operation; cachedReplay; module X; script; Internal; descriptor; key; distinct; decide; keepsJournal; admit; interruptionState; unchanged; published)
  module DocumentEntry = Loading.Registered.Entry library format utcTimestamp databaseSum calculator serverTime configuration postgres
    using (Outcome; inspected; executed; normalized; EntryGoal; Operation; fullOperation; toRecoverable; cachedReplayValue
    ; JournalState; pending; completed; interruptedHasJournal; interruptedMetadataFrame)
  module Reviewing = ReviewOperation.Registered library format database databaseSum calculator
    reviewDependencies reviewCodec postgres reviewBackend
    using (Result; Goal; operation; cachedReplay; interruptedReadback; interruptedKeepsRegistration; interruptedKeepsCancellation)
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
  Result (defeat _) = Defeating.Value
  Result (sweep _) = Sweeping.Result
  Result (sourceWrite _) = Recording.Result
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
  classify expected@(Public.learning (Learning.reviewExperience reviewValue revision)) = reviewWrite expected
  classify (Public.learningQuery request) = learningQuery request
  classify (Public.learningContext queryText project selection) = context (Context.contextSearch queryText project selection)
  classify Public.capabilities = basic Basic.capabilities
  classify (Public.reserveOperation keyValue) = control Controls.reserve keyValue
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
  ... | inj₂ acceptedCall = chooseInput (classify (Request.Invocation.request acceptedCall))
    (tokenForKind (Tools.kind tool) (Request.Invocation.operationToken acceptedCall))
  resolve (privateRead request) = chooseInput (readKind request) nothing

  selectedCertificate : ReviewEnvironment → (call : Call) → Certificate (Choice.kind (resolve call))
  selectedCertificate environment call = certificate environment (Choice.kind (resolve call))
  selectedOperation : (environment : ReviewEnvironment) → (call : Call) →
    Recovery.RecoverableFor Store.World (Input (Choice.kind (resolve call)))
      (Result (Choice.kind (resolve call))) (Goal (Choice.kind (resolve call)))
  selectedOperation environment call = executable (Choice.kind (resolve call)) (selectedCertificate environment call)

  -- The preparation/body join selects these witnesses by the closed kind.
  -- Callers supply neither a script nor a claim that replay is safe.
  module Cached (environment : ReviewEnvironment) where
    module Read = Controls.Readback library postgres using
      (ExecutionContext; Result; ResumableOrCompleted; module SingleKernel; module ProjectJournal
      ; admission; admissionCompletedAnswer; admissionCompletedLookup; admitted; admittedHasPending
      ; answer; completed; pending; returned; undeclaredAbsent; unknownToken)
    data Writer : Kind → Set where
      projectWriter : ∀ {project} → Writer (projectRemoval project)
      patternWriter : ∀ {expected} → Writer (patternWrite expected)
      independentWriter : ∀ {expected} → Writer (independentWrite expected)
      patternRemover : ∀ {expected} → Writer (patternRemoval expected)
      beliefRemover : ∀ {expected} → Writer (beliefRemoval expected)
      relationshipWriter : ∀ {kind expected} → Writer (relationship kind expected)
      groundingWriter : ∀ {kind expected} → Writer (grounding kind expected)
      propagator : ∀ {expected} → Writer (propagation expected)
      decayer : ∀ {expected} → Writer (decay expected)
      documentRemover : ∀ {expected} → Writer (documentRemoval expected)
      defeater : ∀ {expected} → Writer (defeat expected)
      sweeper : ∀ {expected} → Writer (sweep expected)
      sourceWriter : ∀ {expected} → Writer (sourceWrite expected)
      reviewer : ∀ {expected} → Writer (reviewWrite expected)
      documentLoader : ∀ {expected} → Writer (documentLoading expected)

    writerInput : ∀ {kind} → Writer kind → ℕ → Input kind
    writerInput projectWriter token = token
    writerInput patternWriter token = token
    writerInput independentWriter token = token
    writerInput patternRemover token = token
    writerInput beliefRemover token = token
    writerInput relationshipWriter token = token
    writerInput groundingWriter token = token
    writerInput propagator token = token
    writerInput decayer token = token
    writerInput documentRemover token = token
    writerInput defeater token = token
    writerInput sweeper token = token
    writerInput sourceWriter token = token
    writerInput reviewer token = token
    writerInput documentLoader token = token

    writerForKind : (kind : Kind) → Maybe (Writer kind)
    writerForKind (basic _) = nothing
    writerForKind (experiences _) = nothing
    writerForKind (assessments _) = nothing
    writerForKind (intervention _) = nothing
    writerForKind (retrieval _) = nothing
    writerForKind (context _) = nothing
    writerForKind (documentQuery _) = nothing
    writerForKind (correction _) = nothing
    writerForKind (control _ _) = nothing
    writerForKind (projectRemoval _) = just projectWriter
    writerForKind (patternWrite _) = just patternWriter
    writerForKind (independentWrite _) = just independentWriter
    writerForKind (patternRemoval _) = just patternRemover
    writerForKind (beliefRemoval _) = just beliefRemover
    writerForKind (relationship _ _) = just relationshipWriter
    writerForKind (grounding _ _) = just groundingWriter
    writerForKind (propagation _) = just propagator
    writerForKind (decay _) = just decayer
    writerForKind (documentRemoval _) = just documentRemover
    writerForKind (defeat _) = just defeater
    writerForKind (sweep _) = just sweeper
    writerForKind (sourceWrite _) = just sourceWriter
    writerForKind (reviewWrite _) = just reviewer
    writerForKind (documentLoading _) = just documentLoader

    writerName : ∀ {kind} → Writer kind → Text
    writerName projectWriter = Binding.sourceName (Binding.advertised Tools.deleteProject)
    writerName patternWriter = Binding.sourceName (Binding.advertised Tools.insertPattern)
    writerName independentWriter = Binding.sourceName (Binding.advertised Tools.insertBelief)
    writerName patternRemover = Binding.sourceName (Binding.advertised Tools.deletePattern)
    writerName beliefRemover = Binding.sourceName (Binding.advertised Tools.deleteBelief)
    writerName (relationshipWriter {kind}) = Binding.sourceName (Binding.advertised (relationshipTool kind))
    writerName (groundingWriter {kind}) = Binding.sourceName (groundingSource kind)
    writerName propagator = Binding.sourceName (Binding.advertised Tools.propagateFrom)
    writerName decayer = Binding.sourceName (Binding.advertised Tools.decayAll)
    writerName documentRemover = Binding.sourceName (Binding.advertised Tools.clearDocument)
    writerName defeater = Binding.sourceName (Binding.advertised Tools.recordDefeat)
    writerName sweeper = Binding.sourceName (Binding.advertised Tools.sweepExpiredDefeated)
    writerName sourceWriter = Binding.sourceName (Binding.advertised Tools.recordExperience)
    writerName reviewer = Binding.sourceName (Binding.advertised Tools.reviewExperience)
    writerName documentLoader = Binding.sourceName (Binding.advertised Tools.loadDocument)

    stepValue : ∀ {Diagnostic : Set} → Step.Result Diagnostic → Maybe Wire.Value
    stepValue (Step.done raw) = just raw
    stepValue (Step.needsInput _) = nothing
    stepValue Step.needsRecovery = nothing
    stepValue (Step.cancelled _) = nothing

    savedValue : ∀ {kind} → Writer kind → Result kind → Maybe Wire.Value
    savedValue projectWriter reply = just reply
    savedValue (patternWriter {expected}) (PatternGuard.needsInput _) = nothing
    savedValue (patternWriter {expected}) (PatternGuard.executed reply) = stepValue reply
    savedValue (independentWriter {expected}) (IndependentGuard.needsInput _) = nothing
    savedValue (independentWriter {expected}) (IndependentGuard.executed reply) = stepValue (IndependentPublic.Result.value reply)
    savedValue (patternRemover {expected}) (PatternRemovalGuard.needsInput _) = nothing
    savedValue (patternRemover {expected}) (PatternRemovalGuard.executed reply) = stepValue reply
    savedValue (beliefRemover {expected}) (BeliefRemovalGuard.needsInput _) = nothing
    savedValue (beliefRemover {expected}) (BeliefRemovalGuard.executed reply) = stepValue reply
    savedValue (relationshipWriter {kind} {expected}) (RelationshipGuard.needsInput _) = nothing
    savedValue (relationshipWriter {kind} {expected}) (RelationshipGuard.executed reply) = stepValue reply
    savedValue (groundingWriter {kind} {expected}) (GroundingGuard.needsInput _) = nothing
    savedValue (groundingWriter {kind} {expected}) (GroundingGuard.executed reply) = stepValue reply
    savedValue (propagator {expected}) (PropagationGuard.needsInput _) = nothing
    savedValue (propagator {expected}) (PropagationGuard.executed reply) = stepValue reply
    savedValue (decayer {expected}) (DecayGuard.needsInput _) = nothing
    savedValue (decayer {expected}) (DecayGuard.executed reply) = stepValue reply
    savedValue (documentRemover {expected}) (ClearGuard.needsInput _) = nothing
    savedValue (documentRemover {expected}) (ClearGuard.executed reply) = stepValue reply
    savedValue defeater reply = stepValue reply
    savedValue sweeper reply = stepValue reply
    savedValue sourceWriter reply = stepValue reply
    savedValue reviewer reply = stepValue reply
    savedValue documentLoader reply = stepValue (DocumentEntry.normalized reply)

    module Body kind = Recovery.RecoverableFor (executable kind (certificate environment kind)) using (module X; script)

    bodyReplay : ∀ {kind} (writer : Writer kind) token before current binding raw →
      Store.lookupSaved before token Step.resultKey ≡ nothing →
      Store.lookupSaved current token Step.resultKey ≡ just raw →
      Read.admission (writerName writer) token current ≡ Read.returned (Read.completed binding raw) →
      Body.X.Interrupted kind (Body.script kind (writerInput writer token)) before current →
      Σ (Result kind) (λ reply → Body.X.Completed kind
        (Body.script kind (writerInput writer token)) current current reply × savedValue writer reply ≡ just raw)
    bodyReplay (projectWriter {project}) token before current binding raw absent present known cut =
      raw , Project.Registered.cachedReplay (Project.Registered.input token project) before current raw absent cut present , refl
    bodyReplay (patternWriter {expected}) token before current binding raw absent present known cut
      with PatternGuard.completedInterruption expected token before current raw absent present cut
    ... | admitted , sourceCut = PatternGuard.executed (Step.done raw) ,
      PatternGuard.liftReadOnlyCompletion expected token current (Step.done raw)
        (PatternGuard.admittedRetry expected token before current admitted sourceCut)
        (PatternWrite.cachedReplay token before current raw absent present sourceCut) , refl
    bodyReplay (independentWriter {expected}) token before current binding raw absent present known cut
      with IndependentGuard.completedInterruption expected token before current raw absent present cut
    ... | admitted , sourceCut with IndependentPublic.cachedReplayAfterCut token before current raw absent sourceCut present
    ... | reply , complete , value = IndependentGuard.executed reply ,
      IndependentGuard.liftReadOnlyCompletion expected token current reply
        (IndependentGuard.admittedRetry expected token before current admitted sourceCut) complete , cong stepValue value
    bodyReplay (patternRemover {expected}) token before current binding raw absent present known cut
      with PatternRemovalGuard.completedInterruption expected token before current raw absent present cut
    ... | admitted , sourceCut = PatternRemovalGuard.executed (Step.done raw) ,
      PatternRemovalGuard.liftReadOnlyCompletion expected token current (Step.done raw)
        (PatternRemovalGuard.admittedRetry expected token before current admitted sourceCut)
        (PatternRemoval.cachedReplay token before current raw absent present sourceCut) , refl
    bodyReplay (beliefRemover {expected}) token before current binding raw absent present known cut
      with BeliefRemovalGuard.completedInterruption expected token before current raw absent present cut
    ... | admitted , sourceCut = BeliefRemovalGuard.executed (Step.done raw) ,
      BeliefRemovalGuard.liftReadOnlyCompletion expected token current (Step.done raw)
        (BeliefRemovalGuard.admittedRetry expected token before current admitted sourceCut)
        (BeliefRemoval.cachedReplay token before current raw absent present sourceCut) , refl
    bodyReplay (relationshipWriter {kind} {expected}) token before current binding raw absent present known cut
      with RelationshipGuard.completedInterruption kind expected token before current raw absent present cut
    ... | admitted , sourceCut = RelationshipGuard.executed (Step.done raw) ,
      RelationshipGuard.liftReadOnlyCompletion kind expected token current (Step.done raw)
        (RelationshipGuard.admittedRetry kind expected token before current admitted sourceCut)
        (Relationship.cachedReplay kind token before current raw absent present sourceCut) , refl
    bodyReplay (groundingWriter {kind} {expected}) token before current binding raw absent present known cut
      with GroundingGuard.completedInterruption kind expected token before current raw absent present cut
    ... | admitted , sourceCut = GroundingGuard.executed (Step.done raw) ,
      GroundingGuard.liftReadOnlyCompletion kind expected token current (Step.done raw)
        (GroundingGuard.admittedRetry kind expected token before current admitted sourceCut)
        (Grounding.cachedReplay kind token before current raw absent present sourceCut) , refl
    bodyReplay (propagator {expected}) token before current binding raw absent present known cut
      with PropagationGuard.completedInterruption expected token before current raw absent present cut
    ... | admitted , sourceCut = PropagationGuard.executed (Step.done raw) ,
      PropagationGuard.liftReadOnlyCompletion expected token current (Step.done raw)
        (PropagationGuard.admittedRetry expected token before current admitted sourceCut)
        (Propagate.cachedReplay token before current raw absent present sourceCut) , refl
    bodyReplay (decayer {expected}) token before current binding raw absent present known cut
      with DecayGuard.completedInterruption expected token before current raw absent present cut
    ... | admitted , sourceCut = DecayGuard.executed (Step.done raw) ,
      DecayGuard.liftReadOnlyCompletion expected token current (Step.done raw)
        (DecayGuard.admittedRetry expected token before current admitted sourceCut)
        (Decaying.cachedReplay token before current raw absent present sourceCut) , refl
    bodyReplay (documentRemover {expected}) token before current binding raw absent present known cut
      with ClearGuard.completedInterruption expected token before current raw absent present cut
    ... | admitted , sourceCut = ClearGuard.executed (Step.done raw) ,
      ClearGuard.liftReadOnlyCompletion expected token current (Step.done raw)
        (ClearGuard.admittedRetry expected token before current admitted sourceCut)
        (DocumentRemoval.cachedReplay token before current raw absent present sourceCut) , refl
    bodyReplay defeater token before current binding raw absent present known cut =
      Step.done raw , Defeating.cachedReplay token before current raw absent cut present , refl
    bodyReplay sweeper token before current binding raw absent present known cut =
      Step.done raw , Sweeping.cachedReplay token before current raw absent present cut , refl
    bodyReplay sourceWriter token before current binding raw absent present known cut =
      Step.done raw , Recording.cachedReplay token before current raw absent present cut , refl
    bodyReplay reviewer token before current binding raw absent present known cut =
      Step.done raw , Reviewing.cachedReplay environment token current binding raw known , refl
    bodyReplay documentLoader token before current binding raw absent present known cut
      with DocumentEntry.cachedReplayValue token current binding raw known
    ... | reply , complete , value = reply , complete , cong stepValue value


    cachedReplay : ∀ {kind} (writer : Writer kind) token before current binding raw
      (initial : Read.ExecutionContext (writerName writer) token before) →
      Read.admission (writerName writer) token before ≡ Read.admitted initial →
      Body.X.Interrupted kind (Body.script kind (writerInput writer token)) before current →
      Read.admission (writerName writer) token current ≡ Read.returned (Read.completed binding raw) →
      Σ (Result kind) (λ reply → Body.X.Completed kind
        (Body.script kind (writerInput writer token)) current current reply × savedValue writer reply ≡ just raw)
    cachedReplay writer token before current binding raw initial admitted cut known =
      bodyReplay writer token before current binding raw
        (Read.undeclaredAbsent token before _ (Read.ExecutionContext.journal initial)
          Step.resultKey (Read.ExecutionContext.separateResult initial))
        (Read.admissionCompletedLookup (writerName writer) token current binding raw known) known cut


    Resolved : Registered.Descriptor → ℕ → Step.Registration → Set
    Resolved descriptor token registration = Σ (Store.ReservationRow × Store.BindingRow)
      (λ returned → Registered.resolve descriptor token registration ≡ inj₂ returned)

    module SinglePlan descriptor = Controls.Plan.SingletonProjection descriptor using (finalStep; decodedSingle)

    resolvedSingleton : ∀ descriptor operation token before (entry : Read.ExecutionContext operation token before) →
      Resolved descriptor token (Step.registration before) →
      Controls.Plan.Saved.steps (Read.ExecutionContext.plan entry) ≡ (SinglePlan.finalStep descriptor ∷ [])
    resolvedSingleton descriptor operation token before entry (returned , accepted)
      with Registered.resolveMatched descriptor token (Step.registration before) returned accepted
    ... | raw , stored , matched = SinglePlan.decodedSingle descriptor
      (Read.ExecutionContext.rawPlan entry) (Read.ExecutionContext.plan entry)
      (subst (λ actual → Registered.Plan.matches descriptor actual ≡ true) (sym sameRaw) matched)
      (Read.ExecutionContext.decoded entry)
      where
      sameRaw = Maybes.just-injective (trans (sym (Read.ExecutionContext.originalPlan entry)) stored)

    patternResolved : ∀ (input : PatternWrite.Internal) registration → PatternWrite.admit input registration ≡ nothing →
      Resolved (PatternWrite.descriptor) (proj₁ input) registration
    patternResolved input registration admitted
      with Registered.resolve (PatternWrite.descriptor) (proj₁ input) registration in resolved
    ... | inj₁ fault with admitted
    ... | ()
    patternResolved input registration admitted | inj₂ returned = returned , resolved

    patternRemovalResolved : ∀ (token : ℕ) registration → PatternRemoval.admit token registration ≡ nothing →
      Resolved (PatternRemoval.descriptor) (token) registration
    patternRemovalResolved token registration admitted
      with Registered.resolve (PatternRemoval.descriptor) (token) registration in resolved
    ... | inj₁ fault with admitted
    ... | ()
    patternRemovalResolved token registration admitted | inj₂ returned = returned , resolved

    relationshipResolved : ∀ (kind : Edges.Kind) (token : ℕ) registration → Relationship.admit kind token registration ≡ nothing →
      Resolved (Edges.descriptor kind) (token) registration
    relationshipResolved kind token registration admitted
      with Registered.resolve (Edges.descriptor kind) (token) registration in resolved
    ... | inj₁ fault with admitted
    ... | ()
    relationshipResolved kind token registration admitted | inj₂ returned = returned , resolved

    beliefRemovalResolved : ∀ (token : ℕ) registration → BeliefRemoval.admit token registration ≡ nothing →
      Resolved (BeliefRemoval.descriptor) (token) registration
    beliefRemovalResolved token registration admitted
      with Registered.resolve (BeliefRemoval.descriptor) (token) registration in resolved
    ... | inj₁ fault with admitted
    ... | ()
    beliefRemovalResolved token registration admitted | inj₂ returned = returned , resolved

    groundingResolved : ∀ (kind : Ground.Kind) (token : ℕ) registration → Grounding.admit kind token registration ≡ nothing →
      Resolved (Grounding.descriptor kind) (token) registration
    groundingResolved kind token registration admitted
      with Registered.resolve (Grounding.descriptor kind) (token) registration in resolved
    ... | inj₁ fault with admitted
    ... | ()
    groundingResolved kind token registration admitted | inj₂ returned = returned , resolved

    propagationResolved : ∀ (token : ℕ) registration → Propagate.admit token registration ≡ nothing →
      Resolved (Propagate.descriptor) (token) registration
    propagationResolved token registration admitted
      with Registered.resolve (Propagate.descriptor) (token) registration in resolved
    ... | inj₁ fault with admitted
    ... | ()
    propagationResolved token registration admitted | inj₂ returned = returned , resolved

    decayResolved : ∀ (token : ℕ) registration → Decaying.admit token registration ≡ nothing →
      Resolved (Decaying.descriptor) (token) registration
    decayResolved token registration admitted
      with Registered.resolve (Decaying.descriptor) (token) registration in resolved
    ... | inj₁ fault with admitted
    ... | ()
    decayResolved token registration admitted | inj₂ returned = returned , resolved

    clearResolved : ∀ (token : ℕ) registration → DocumentRemoval.admit token registration ≡ nothing →
      Resolved (DocumentRemoval.descriptor) (token) registration
    clearResolved token registration admitted
      with Registered.resolve (DocumentRemoval.descriptor) (token) registration in resolved
    ... | inj₁ fault with admitted
    ... | ()
    clearResolved token registration admitted | inj₂ returned = returned , resolved

    sourceResolved : ∀ (input : Recording.Internal) registration → Recording.admit input registration ≡ nothing →
      Resolved (Recording.descriptor) (proj₁ input) registration
    sourceResolved input registration admitted
      with Registered.resolve (Recording.descriptor) (proj₁ input) registration in resolved
    ... | inj₁ fault with admitted
    ... | ()
    sourceResolved input registration admitted | inj₂ returned = returned , resolved


    module PatternKernel = Read.SingleKernel (PatternWrite.Internal) _ proj₁ (λ input → PatternWrite.key (proj₁ input)) (λ input → PatternWrite.distinct (proj₁ input))
      (PatternWrite.decide) (PatternWrite.keepsJournal) (PatternWrite.admit)
      using (executeReadback; executeStateOutcome; executeStateReadback; module Saved)

    patternPublishedReadback : ∀ operation (input : PatternWrite.Internal) before current
      (entry : Read.ExecutionContext operation (proj₁ input) before) value →
      Read.admission operation (proj₁ input) before ≡ Read.admitted entry →
      (current , Step.done value) ≡ PatternKernel.Saved.execute input before →
      Read.ResumableOrCompleted operation (proj₁ input) current
    patternPublishedReadback operation input before current entry value admitted observed =
      PatternKernel.executeReadback operation input before current entry
        (SinglePlan.finalStep (PatternWrite.descriptor)) value admitted
        (resolvedSingleton (PatternWrite.descriptor) operation (proj₁ input) before entry
          (patternResolved input (Step.registration before)
            (PatternKernel.Saved.doneIsAdmitted input before current value (sym observed)))) refl observed

    module PatternRemovalKernel = Read.SingleKernel (ℕ) _ (λ input → input) (PatternRemoval.key) (PatternRemoval.distinct)
      (PatternRemoval.decide) (PatternRemoval.keepsJournal) (PatternRemoval.admit)
      using (executeReadback; executeStateOutcome; executeStateReadback; module Saved)

    patternRemovalPublishedReadback : ∀ operation (input : ℕ) before current
      (entry : Read.ExecutionContext operation (input) before) value →
      Read.admission operation (input) before ≡ Read.admitted entry →
      (current , Step.done value) ≡ PatternRemovalKernel.Saved.execute input before →
      Read.ResumableOrCompleted operation (input) current
    patternRemovalPublishedReadback operation input before current entry value admitted observed =
      PatternRemovalKernel.executeReadback operation input before current entry
        (SinglePlan.finalStep (PatternRemoval.descriptor)) value admitted
        (resolvedSingleton (PatternRemoval.descriptor) operation (input) before entry
          (patternRemovalResolved input (Step.registration before)
            (PatternRemovalKernel.Saved.doneIsAdmitted input before current value (sym observed)))) refl observed

    module RelationshipKernel kind = Read.SingleKernel (ℕ) _ (λ input → input) (Relationship.key kind) (Relationship.distinct kind)
      (Relationship.decide kind) (Relationship.keepsJournal kind) (Relationship.admit kind)
      using (executeReadback; executeStateOutcome; executeStateReadback; module Saved)

    relationshipPublishedReadback : ∀ (kind : Edges.Kind) operation (input : ℕ) before current
      (entry : Read.ExecutionContext operation (input) before) value →
      Read.admission operation (input) before ≡ Read.admitted entry →
      (current , Step.done value) ≡ RelationshipKernel.Saved.execute kind input before →
      Read.ResumableOrCompleted operation (input) current
    relationshipPublishedReadback kind operation input before current entry value admitted observed =
      RelationshipKernel.executeReadback kind operation input before current entry
        (SinglePlan.finalStep (Edges.descriptor kind)) value admitted
        (resolvedSingleton (Edges.descriptor kind) operation (input) before entry
          (relationshipResolved kind input (Step.registration before)
            (RelationshipKernel.Saved.doneIsAdmitted kind input before current value (sym observed)))) refl observed

    module BeliefRemovalKernel = Read.SingleKernel (ℕ × ℤ) _ proj₁ (λ input → BeliefRemoval.key (proj₁ input)) (λ input → BeliefRemoval.distinct (proj₁ input))
      (BeliefRemoval.decide) (BeliefRemoval.keepsJournal) (λ input → BeliefRemoval.admit (proj₁ input))
      using (executeReadback; executeStateOutcome; executeStateReadback; module Saved)

    beliefRemovalPublishedReadback : ∀ operation (input : ℕ × ℤ) before current
      (entry : Read.ExecutionContext operation (proj₁ input) before) value →
      Read.admission operation (proj₁ input) before ≡ Read.admitted entry →
      (current , Step.done value) ≡ BeliefRemovalKernel.Saved.execute input before →
      Read.ResumableOrCompleted operation (proj₁ input) current
    beliefRemovalPublishedReadback operation input before current entry value admitted observed =
      BeliefRemovalKernel.executeReadback operation input before current entry
        (SinglePlan.finalStep (BeliefRemoval.descriptor)) value admitted
        (resolvedSingleton (BeliefRemoval.descriptor) operation (proj₁ input) before entry
          (beliefRemovalResolved proj₁ input (Step.registration before)
            (BeliefRemovalKernel.Saved.doneIsAdmitted input before current value (sym observed)))) refl observed

    module GroundingKernel kind = Read.SingleKernel (ℕ × ℤ) _ proj₁ (λ input → Grounding.key kind (proj₁ input)) (λ input → Grounding.distinct kind (proj₁ input))
      (Grounding.decide kind) (Grounding.keepsJournal kind) (λ input → Grounding.admit kind (proj₁ input))
      using (executeReadback; executeStateOutcome; executeStateReadback; module Saved)

    groundingPublishedReadback : ∀ (kind : Ground.Kind) operation (input : ℕ × ℤ) before current
      (entry : Read.ExecutionContext operation (proj₁ input) before) value →
      Read.admission operation (proj₁ input) before ≡ Read.admitted entry →
      (current , Step.done value) ≡ GroundingKernel.Saved.execute kind input before →
      Read.ResumableOrCompleted operation (proj₁ input) current
    groundingPublishedReadback kind operation input before current entry value admitted observed =
      GroundingKernel.executeReadback kind operation input before current entry
        (SinglePlan.finalStep (Grounding.descriptor kind)) value admitted
        (resolvedSingleton (Grounding.descriptor kind) operation (proj₁ input) before entry
          (groundingResolved kind (proj₁ input) (Step.registration before)
            (GroundingKernel.Saved.doneIsAdmitted kind input before current value (sym observed)))) refl observed

    module PropagationKernel = Read.SingleKernel (ℕ × ℤ) _ proj₁ (λ input → Propagate.key (proj₁ input)) (λ input → Propagate.distinct (proj₁ input))
      (Propagate.decide) (Propagate.keepsJournal) (λ input → Propagate.admit (proj₁ input))
      using (executeReadback; executeStateOutcome; executeStateReadback; module Saved)

    propagationPublishedReadback : ∀ operation (input : ℕ × ℤ) before current
      (entry : Read.ExecutionContext operation (proj₁ input) before) value →
      Read.admission operation (proj₁ input) before ≡ Read.admitted entry →
      (current , Step.done value) ≡ PropagationKernel.Saved.execute input before →
      Read.ResumableOrCompleted operation (proj₁ input) current
    propagationPublishedReadback operation input before current entry value admitted observed =
      PropagationKernel.executeReadback operation input before current entry
        (SinglePlan.finalStep (Propagate.descriptor)) value admitted
        (resolvedSingleton (Propagate.descriptor) operation (proj₁ input) before entry
          (propagationResolved proj₁ input (Step.registration before)
            (PropagationKernel.Saved.doneIsAdmitted input before current value (sym observed)))) refl observed

    module DecayKernel = Read.SingleKernel (ℕ × ℤ) _ proj₁ (λ input → Decaying.key (proj₁ input)) (λ input → Decaying.distinct (proj₁ input))
      (Decaying.decide) (Decaying.keepsJournal) (λ input → Decaying.admit (proj₁ input))
      using (executeReadback; executeStateOutcome; executeStateReadback; module Saved)

    decayPublishedReadback : ∀ operation (input : ℕ × ℤ) before current
      (entry : Read.ExecutionContext operation (proj₁ input) before) value →
      Read.admission operation (proj₁ input) before ≡ Read.admitted entry →
      (current , Step.done value) ≡ DecayKernel.Saved.execute input before →
      Read.ResumableOrCompleted operation (proj₁ input) current
    decayPublishedReadback operation input before current entry value admitted observed =
      DecayKernel.executeReadback operation input before current entry
        (SinglePlan.finalStep (Decaying.descriptor)) value admitted
        (resolvedSingleton (Decaying.descriptor) operation (proj₁ input) before entry
          (decayResolved proj₁ input (Step.registration before)
            (DecayKernel.Saved.doneIsAdmitted input before current value (sym observed)))) refl observed

    module ClearKernel = Read.SingleKernel (ℕ × ℤ) _ proj₁ (λ input → DocumentRemoval.key (proj₁ input)) (λ input → DocumentRemoval.distinct (proj₁ input))
      (DocumentRemoval.decide) (DocumentRemoval.keepsJournal) (λ input → DocumentRemoval.admit (proj₁ input))
      using (executeReadback; executeStateOutcome; executeStateReadback; module Saved)

    clearPublishedReadback : ∀ operation (input : ℕ × ℤ) before current
      (entry : Read.ExecutionContext operation (proj₁ input) before) value →
      Read.admission operation (proj₁ input) before ≡ Read.admitted entry →
      (current , Step.done value) ≡ ClearKernel.Saved.execute input before →
      Read.ResumableOrCompleted operation (proj₁ input) current
    clearPublishedReadback operation input before current entry value admitted observed =
      ClearKernel.executeReadback operation input before current entry
        (SinglePlan.finalStep (DocumentRemoval.descriptor)) value admitted
        (resolvedSingleton (DocumentRemoval.descriptor) operation (proj₁ input) before entry
          (clearResolved proj₁ input (Step.registration before)
            (ClearKernel.Saved.doneIsAdmitted input before current value (sym observed)))) refl observed

    module SourceKernel = Read.SingleKernel (Recording.Internal) _ proj₁ (λ input → Recording.key (proj₁ input)) (λ input → Recording.distinct (proj₁ input))
      (Recording.decide) (Recording.keepsJournal) (Recording.admit)
      using (executeReadback; executeStateOutcome; executeStateReadback; module Saved)

    sourcePublishedReadback : ∀ operation (input : Recording.Internal) before current
      (entry : Read.ExecutionContext operation (proj₁ input) before) value →
      Read.admission operation (proj₁ input) before ≡ Read.admitted entry →
      (current , Step.done value) ≡ SourceKernel.Saved.execute input before →
      Read.ResumableOrCompleted operation (proj₁ input) current
    sourcePublishedReadback operation input before current entry value admitted observed =
      SourceKernel.executeReadback operation input before current entry
        (SinglePlan.finalStep (Recording.descriptor)) value admitted
        (resolvedSingleton (Recording.descriptor) operation (proj₁ input) before entry
          (sourceResolved input (Step.registration before)
            (SourceKernel.Saved.doneIsAdmitted input before current value (sym observed)))) refl observed

    patternReadback : ∀ operation token before current (entry : Read.ExecutionContext operation token before) →
      Read.admission operation token before ≡ Read.admitted entry →
      PatternWrite.X.Interrupted (PatternWrite.script token) before current → Read.ResumableOrCompleted operation token current
    patternReadback operation token before current entry admitted cut with PatternWrite.interruptionState token before current cut
    ... | inj₁ refl = inj₁ (entry , admitted)
    ... | inj₂ (metadata , physical) with PatternKernel.executeStateOutcome (token , metadata) before current physical
    ... | inj₁ refl = inj₁ (entry , admitted)
    ... | inj₂ (value , observed) = patternPublishedReadback operation (token , metadata) before current entry value admitted observed

    patternRemovalReadback : ∀ operation token before current (entry : Read.ExecutionContext operation token before) →
      Read.admission operation token before ≡ Read.admitted entry →
      PatternRemovalKernel.Saved.X.Interrupted (PatternRemovalKernel.Saved.script token) before current →
      Read.ResumableOrCompleted operation token current
    patternRemovalReadback operation token before current entry admitted cut
      with PatternRemovalKernel.Saved.interruptedDoneOrUnchanged token before current cut
    ... | inj₁ refl = inj₁ (entry , admitted)
    ... | inj₂ (value , observed) = patternRemovalPublishedReadback operation token before current entry value admitted observed

    relationshipReadback : ∀ kind operation token before current (entry : Read.ExecutionContext operation token before) →
      Read.admission operation token before ≡ Read.admitted entry →
      RelationshipKernel.Saved.X.Interrupted kind (RelationshipKernel.Saved.script kind token) before current →
      Read.ResumableOrCompleted operation token current
    relationshipReadback kind operation token before current entry admitted cut
      with RelationshipKernel.Saved.interruptedDoneOrUnchanged kind token before current cut
    ... | inj₁ refl = inj₁ (entry , admitted)
    ... | inj₂ (value , observed) = relationshipPublishedReadback kind operation token before current entry value admitted observed

    beliefRemovalReadback : ∀ operation token before current (entry : Read.ExecutionContext operation token before) →
      Read.admission operation token before ≡ Read.admitted entry →
      BeliefRemoval.X.Interrupted (BeliefRemoval.script token) before current → Read.ResumableOrCompleted operation token current
    beliefRemovalReadback operation token before current entry admitted cut with BeliefRemoval.interruptionState token before current cut
    ... | Step.Observed.unchanged refl = inj₁ (entry , admitted)
    ... | Step.Observed.published time value observed = beliefRemovalPublishedReadback operation (token , time) before current entry value admitted observed

    groundingReadback : ∀ kind operation token before current (entry : Read.ExecutionContext operation token before) →
      Read.admission operation token before ≡ Read.admitted entry →
      Grounding.X.Interrupted kind (Grounding.script kind token) before current → Read.ResumableOrCompleted operation token current
    groundingReadback kind operation token before current entry admitted cut with Grounding.interruptionState kind token before current cut
    ... | Step.Observed.unchanged refl = inj₁ (entry , admitted)
    ... | Step.Observed.published time value observed = groundingPublishedReadback kind operation (token , time) before current entry value admitted observed

    propagationReadback : ∀ operation token before current (entry : Read.ExecutionContext operation token before) →
      Read.admission operation token before ≡ Read.admitted entry →
      Propagate.X.Interrupted (Propagate.script token) before current → Read.ResumableOrCompleted operation token current
    propagationReadback operation token before current entry admitted cut with Propagate.interruptionState token before current cut
    ... | Step.Observed.unchanged refl = inj₁ (entry , admitted)
    ... | Step.Observed.published time value observed = propagationPublishedReadback operation (token , time) before current entry value admitted observed

    decayReadback : ∀ operation token before current (entry : Read.ExecutionContext operation token before) →
      Read.admission operation token before ≡ Read.admitted entry →
      Decaying.X.Interrupted (Decaying.script token) before current → Read.ResumableOrCompleted operation token current
    decayReadback operation token before current entry admitted cut with Decaying.interruptionState token before current cut
    ... | Step.Observed.unchanged refl = inj₁ (entry , admitted)
    ... | Step.Observed.published time value observed = decayPublishedReadback operation (token , time) before current entry value admitted observed

    clearReadback : ∀ operation token before current (entry : Read.ExecutionContext operation token before) →
      Read.admission operation token before ≡ Read.admitted entry →
      DocumentRemoval.X.Interrupted (DocumentRemoval.script token) before current → Read.ResumableOrCompleted operation token current
    clearReadback operation token before current entry admitted cut with DocumentRemoval.interruptionState token before current cut
    ... | Step.Observed.unchanged refl = inj₁ (entry , admitted)
    ... | Step.Observed.published time value observed = clearPublishedReadback operation (token , time) before current entry value admitted observed

    sourceReadback : ∀ operation token before current (entry : Read.ExecutionContext operation token before) →
      Read.admission operation token before ≡ Read.admitted entry →
      Recording.X.Interrupted (Recording.script token) before current → Read.ResumableOrCompleted operation token current
    sourceReadback operation token before current entry admitted cut with Recording.interruptionState token before current cut
    ... | Recording.unchanged refl = inj₁ (entry , admitted)
    ... | Recording.published metadata value valid observed = sourcePublishedReadback operation (token , metadata) before current entry value admitted observed


    MetadataFrame : ℕ → Store.World → Store.World → Set
    MetadataFrame token before current = Step.registration current ≡ Step.registration before ×
      Store.lookupCancellation current token ≡ Store.lookupCancellation before token

    patternMetadata : ∀ token before current → PatternWrite.X.Interrupted (PatternWrite.script token) before current →
      MetadataFrame token before current
    patternMetadata token before current cut with PatternWrite.interruptionState token before current cut
    ... | inj₁ refl = refl , refl
    ... | inj₂ (metadata , physical) =
      trans (cong Step.registration physical) (PatternKernel.Saved.registrationUnchanged (token , metadata) before) ,
      trans (cong (λ world → Store.lookupCancellation world token) physical)
        (PatternKernel.Saved.cancellationUnchanged token (token , metadata) before)

    patternRemovalMetadata : ∀ token before current →
      PatternRemovalKernel.Saved.X.Interrupted (PatternRemovalKernel.Saved.script token) before current → MetadataFrame token before current
    patternRemovalMetadata token before current cut = PatternRemovalKernel.Saved.interruptedKeepsRegistration token before current cut ,
      PatternRemovalKernel.Saved.interruptedKeepsCancellation token token before current cut

    relationshipMetadata : ∀ kind token before current →
      RelationshipKernel.Saved.X.Interrupted kind (RelationshipKernel.Saved.script kind token) before current → MetadataFrame token before current
    relationshipMetadata kind token before current cut = RelationshipKernel.Saved.interruptedKeepsRegistration kind token before current cut ,
      RelationshipKernel.Saved.interruptedKeepsCancellation kind token token before current cut

    sourceMetadata : ∀ token before current → Recording.X.Interrupted (Recording.script token) before current →
      MetadataFrame token before current
    sourceMetadata token before current cut with Recording.interruptionState token before current cut
    ... | Recording.unchanged refl = refl , refl
    ... | Recording.published metadata value valid physical =
      trans (cong Step.registration (cong proj₁ physical)) (SourceKernel.Saved.registrationUnchanged (token , metadata) before) ,
      trans (cong (λ world → Store.lookupCancellation world token) (cong proj₁ physical))
        (SourceKernel.Saved.cancellationUnchanged token (token , metadata) before)

    patternGuardedReadback : ∀ expected operation token before current (entry : Read.ExecutionContext operation token before) →
      Read.admission operation token before ≡ Read.admitted entry →
      PatternGuard.X.Interrupted expected (PatternGuard.script expected token) before current →
      Read.ResumableOrCompleted operation token current
    patternGuardedReadback expected operation token before current entry admitted cut
      with PatternGuard.interruptionMeaning expected token before current cut
    ... | inj₁ refl = inj₁ (entry , admitted)
    ... | inj₂ (matched , actualCut) = patternReadback operation token before current entry admitted actualCut

    patternGuardedMetadata : ∀ expected token before current →
      PatternGuard.X.Interrupted expected (PatternGuard.script expected token) before current → MetadataFrame token before current
    patternGuardedMetadata expected token before current cut
      with PatternGuard.interruptionMeaning expected token before current cut
    ... | inj₁ refl = refl , refl
    ... | inj₂ (matched , actualCut) = patternMetadata token before current actualCut

    patternRemovalGuardedReadback : ∀ expected operation token before current (entry : Read.ExecutionContext operation token before) →
      Read.admission operation token before ≡ Read.admitted entry →
      PatternRemovalGuard.X.Interrupted expected (PatternRemovalGuard.script expected token) before current →
      Read.ResumableOrCompleted operation token current
    patternRemovalGuardedReadback expected operation token before current entry admitted cut
      with PatternRemovalGuard.interruptionMeaning expected token before current cut
    ... | inj₁ refl = inj₁ (entry , admitted)
    ... | inj₂ (matched , actualCut) = patternRemovalReadback operation token before current entry admitted actualCut

    patternRemovalGuardedMetadata : ∀ expected token before current →
      PatternRemovalGuard.X.Interrupted expected (PatternRemovalGuard.script expected token) before current → MetadataFrame token before current
    patternRemovalGuardedMetadata expected token before current cut
      with PatternRemovalGuard.interruptionMeaning expected token before current cut
    ... | inj₁ refl = refl , refl
    ... | inj₂ (matched , actualCut) = patternRemovalMetadata token before current actualCut

    relationshipGuardedReadback : ∀ kind expected operation token before current (entry : Read.ExecutionContext operation token before) →
      Read.admission operation token before ≡ Read.admitted entry →
      RelationshipGuard.X.Interrupted kind expected (RelationshipGuard.script kind expected token) before current →
      Read.ResumableOrCompleted operation token current
    relationshipGuardedReadback kind expected operation token before current entry admitted cut
      with RelationshipGuard.interruptionMeaning kind expected token before current cut
    ... | inj₁ refl = inj₁ (entry , admitted)
    ... | inj₂ (matched , actualCut) = relationshipReadback kind operation token before current entry admitted actualCut

    relationshipGuardedMetadata : ∀ kind expected token before current →
      RelationshipGuard.X.Interrupted kind expected (RelationshipGuard.script kind expected token) before current → MetadataFrame token before current
    relationshipGuardedMetadata kind expected token before current cut
      with RelationshipGuard.interruptionMeaning kind expected token before current cut
    ... | inj₁ refl = refl , refl
    ... | inj₂ (matched , actualCut) = relationshipMetadata kind token before current actualCut

    beliefRemovalGuardedReadback : ∀ expected operation token before current (entry : Read.ExecutionContext operation token before) →
      Read.admission operation token before ≡ Read.admitted entry →
      BeliefRemovalGuard.X.Interrupted expected (BeliefRemovalGuard.script expected token) before current →
      Read.ResumableOrCompleted operation token current
    beliefRemovalGuardedReadback expected operation token before current entry admitted cut
      with BeliefRemovalGuard.interruptionMeaning expected token before current cut
    ... | inj₁ refl = inj₁ (entry , admitted)
    ... | inj₂ (matched , actualCut) = beliefRemovalReadback operation token before current entry admitted actualCut

    beliefRemovalGuardedMetadata : ∀ expected token before current →
      BeliefRemovalGuard.X.Interrupted expected (BeliefRemovalGuard.script expected token) before current → MetadataFrame token before current
    beliefRemovalGuardedMetadata expected token before current cut
      with BeliefRemovalGuard.interruptionMeaning expected token before current cut
    ... | inj₁ refl = refl , refl
    ... | inj₂ (matched , actualCut) = BeliefRemoval.interruptedKeepsRegistration token before current actualCut ,
      BeliefRemoval.interruptedKeepsCancellation token token before current actualCut

    groundingGuardedReadback : ∀ kind expected operation token before current (entry : Read.ExecutionContext operation token before) →
      Read.admission operation token before ≡ Read.admitted entry →
      GroundingGuard.X.Interrupted kind expected (GroundingGuard.script kind expected token) before current →
      Read.ResumableOrCompleted operation token current
    groundingGuardedReadback kind expected operation token before current entry admitted cut
      with GroundingGuard.interruptionMeaning kind expected token before current cut
    ... | inj₁ refl = inj₁ (entry , admitted)
    ... | inj₂ (matched , actualCut) = groundingReadback kind operation token before current entry admitted actualCut

    groundingGuardedMetadata : ∀ kind expected token before current →
      GroundingGuard.X.Interrupted kind expected (GroundingGuard.script kind expected token) before current → MetadataFrame token before current
    groundingGuardedMetadata kind expected token before current cut
      with GroundingGuard.interruptionMeaning kind expected token before current cut
    ... | inj₁ refl = refl , refl
    ... | inj₂ (matched , actualCut) = Grounding.interruptedKeepsRegistration kind token before current actualCut ,
      Grounding.interruptedKeepsCancellation kind token token before current actualCut

    propagationGuardedReadback : ∀ expected operation token before current (entry : Read.ExecutionContext operation token before) →
      Read.admission operation token before ≡ Read.admitted entry →
      PropagationGuard.X.Interrupted expected (PropagationGuard.script expected token) before current →
      Read.ResumableOrCompleted operation token current
    propagationGuardedReadback expected operation token before current entry admitted cut
      with PropagationGuard.interruptionMeaning expected token before current cut
    ... | inj₁ refl = inj₁ (entry , admitted)
    ... | inj₂ (matched , actualCut) = propagationReadback operation token before current entry admitted actualCut

    propagationGuardedMetadata : ∀ expected token before current →
      PropagationGuard.X.Interrupted expected (PropagationGuard.script expected token) before current → MetadataFrame token before current
    propagationGuardedMetadata expected token before current cut
      with PropagationGuard.interruptionMeaning expected token before current cut
    ... | inj₁ refl = refl , refl
    ... | inj₂ (matched , actualCut) = Propagate.interruptedKeepsRegistration token before current actualCut ,
      Propagate.interruptedKeepsCancellation token token before current actualCut

    decayGuardedReadback : ∀ expected operation token before current (entry : Read.ExecutionContext operation token before) →
      Read.admission operation token before ≡ Read.admitted entry →
      DecayGuard.X.Interrupted expected (DecayGuard.script expected token) before current →
      Read.ResumableOrCompleted operation token current
    decayGuardedReadback expected operation token before current entry admitted cut
      with DecayGuard.interruptionMeaning expected token before current cut
    ... | inj₁ refl = inj₁ (entry , admitted)
    ... | inj₂ (matched , actualCut) = decayReadback operation token before current entry admitted actualCut

    decayGuardedMetadata : ∀ expected token before current →
      DecayGuard.X.Interrupted expected (DecayGuard.script expected token) before current → MetadataFrame token before current
    decayGuardedMetadata expected token before current cut
      with DecayGuard.interruptionMeaning expected token before current cut
    ... | inj₁ refl = refl , refl
    ... | inj₂ (matched , actualCut) = Decaying.interruptedKeepsRegistration token before current actualCut ,
      Decaying.interruptedKeepsCancellation token token before current actualCut

    clearGuardedReadback : ∀ expected operation token before current (entry : Read.ExecutionContext operation token before) →
      Read.admission operation token before ≡ Read.admitted entry →
      ClearGuard.X.Interrupted expected (ClearGuard.script expected token) before current →
      Read.ResumableOrCompleted operation token current
    clearGuardedReadback expected operation token before current entry admitted cut
      with ClearGuard.interruptionMeaning expected token before current cut
    ... | inj₁ refl = inj₁ (entry , admitted)
    ... | inj₂ (matched , actualCut) = clearReadback operation token before current entry admitted actualCut

    clearGuardedMetadata : ∀ expected token before current →
      ClearGuard.X.Interrupted expected (ClearGuard.script expected token) before current → MetadataFrame token before current
    clearGuardedMetadata expected token before current cut
      with ClearGuard.interruptionMeaning expected token before current cut
    ... | inj₁ refl = refl , refl
    ... | inj₂ (matched , actualCut) = DocumentRemoval.interruptedKeepsRegistration token before current actualCut ,
      DocumentRemoval.interruptedKeepsCancellation token token before current actualCut


    module IndependentJournal = IndependentPublic.Journal postgres using (interruptedReadback; interruptedFrame)
    module DefeatJournal = Defeat.Registered.Journal library databaseSum calculator serverTime postgres
      using (interruptedReadback; interruptedFrame)
    module SweepJournal = Sweep.Registered.Journal library format databaseSum calculator sweepObservation postgres
      using (interruptedReadback; interruptedAdmission; interruptedFrame)

    independentGuardedReadback : ∀ expected operation token before current (entry : Read.ExecutionContext operation token before) →
      operation ≡ toList "insert_belief" → Read.admission operation token before ≡ Read.admitted entry →
      IndependentGuard.X.Interrupted expected (IndependentGuard.script expected token) before current →
      Read.ResumableOrCompleted operation token current
    independentGuardedReadback expected .(toList "insert_belief") token before current entry refl admitted cut
      with IndependentGuard.interruptionMeaning expected token before current cut
    ... | inj₁ refl = inj₁ (entry , admitted)
    ... | inj₂ (matched , actualCut) = IndependentJournal.interruptedReadback token before current entry admitted actualCut

    independentGuardedMetadata : ∀ expected token before current →
      IndependentGuard.X.Interrupted expected (IndependentGuard.script expected token) before current → MetadataFrame token before current
    independentGuardedMetadata expected token before current cut
      with IndependentGuard.interruptionMeaning expected token before current cut
    ... | inj₁ refl = refl , refl
    ... | inj₂ (matched , actualCut) = IndependentJournal.interruptedFrame token before current actualCut

    documentReadback : ∀ expected token before current (entry : Read.ExecutionContext (toList "load_document") token before) →
      Read.admission (toList "load_document") token before ≡ Read.admitted entry →
      Body.X.Interrupted (documentLoading expected) (Body.script (documentLoading expected) token) before current →
      Read.ResumableOrCompleted (toList "load_document") token current
    documentReadback expected token before current entry admitted cut with DocumentEntry.interruptedHasJournal token before current entry admitted cut
    ... | DocumentEntry.pending actual known = inj₁ (actual , known)
    ... | DocumentEntry.completed binding raw known replay = inj₂ (binding , raw , known)


    pendingSweepUnchanged : ∀ expected token before current (entry : Read.ExecutionContext (toList "sweep_expired_defeated") token before) →
      Read.admission (toList "sweep_expired_defeated") token before ≡ Read.admitted entry →
      Body.X.Interrupted (sweep expected) (Body.script (sweep expected) token) before current →
      Binding.Creating.Resumable library postgres (Read.answer token current) → current ≡ before
    pendingSweepUnchanged expected token before current entry admitted cut possible
      with SweepJournal.interruptedReadback token before current entry admitted cut
    ... | inj₁ unchanged = unchanged
    ... | inj₂ (binding , raw , completed) = ⊥-elim
      (subst (Binding.Creating.Resumable library postgres)
        (Read.admissionCompletedAnswer (toList "sweep_expired_defeated") token current binding raw completed) possible)


    bodyReadback : ∀ {kind} (writer : Writer kind) token before current
      (entry : Read.ExecutionContext (writerName writer) token before) →
      Read.admission (writerName writer) token before ≡ Read.admitted entry →
      Body.X.Interrupted kind (Body.script kind (writerInput writer token)) before current →
      Read.ResumableOrCompleted (writerName writer) token current
    bodyReadback (projectWriter {project}) token before current entry admitted cut =
      Read.ProjectJournal.interruptedReadback (Project.Registered.input token project) before current entry admitted cut
    bodyReadback (patternWriter {expected}) token before current entry admitted cut =
      patternGuardedReadback expected _ token before current entry admitted cut
    bodyReadback (independentWriter {expected}) token before current entry admitted cut =
      independentGuardedReadback expected _ token before current entry refl admitted cut
    bodyReadback (patternRemover {expected}) token before current entry admitted cut =
      patternRemovalGuardedReadback expected _ token before current entry admitted cut
    bodyReadback (beliefRemover {expected}) token before current entry admitted cut =
      beliefRemovalGuardedReadback expected _ token before current entry admitted cut
    bodyReadback (relationshipWriter {kind} {expected}) token before current entry admitted cut =
      relationshipGuardedReadback kind expected _ token before current entry admitted cut
    bodyReadback (groundingWriter {kind} {expected}) token before current entry admitted cut =
      groundingGuardedReadback kind expected _ token before current entry admitted cut
    bodyReadback (propagator {expected}) token before current entry admitted cut =
      propagationGuardedReadback expected _ token before current entry admitted cut
    bodyReadback (decayer {expected}) token before current entry admitted cut =
      decayGuardedReadback expected _ token before current entry admitted cut
    bodyReadback (documentRemover {expected}) token before current entry admitted cut =
      clearGuardedReadback expected _ token before current entry admitted cut
    bodyReadback defeater token before current entry admitted cut = DefeatJournal.interruptedReadback token before current entry admitted cut
    bodyReadback sweeper token before current entry admitted cut = SweepJournal.interruptedAdmission token before current entry admitted cut
    bodyReadback sourceWriter token before current entry admitted cut = sourceReadback _ token before current entry admitted cut
    bodyReadback reviewer token before current entry admitted cut = Reviewing.interruptedReadback token before current entry admitted cut
    bodyReadback (documentLoader {expected}) token before current entry admitted cut = documentReadback expected token before current entry admitted cut

    bodyMetadata : ∀ {kind} (writer : Writer kind) token before current →
      Body.X.Interrupted kind (Body.script kind (writerInput writer token)) before current → MetadataFrame token before current
    bodyMetadata (projectWriter {project}) token before current cut =
      Read.ProjectJournal.interruptedFrame (Project.Registered.input token project) before current cut
    bodyMetadata (patternWriter {expected}) token before current cut = patternGuardedMetadata expected token before current cut
    bodyMetadata (independentWriter {expected}) token before current cut = independentGuardedMetadata expected token before current cut
    bodyMetadata (patternRemover {expected}) token before current cut = patternRemovalGuardedMetadata expected token before current cut
    bodyMetadata (beliefRemover {expected}) token before current cut = beliefRemovalGuardedMetadata expected token before current cut
    bodyMetadata (relationshipWriter {kind} {expected}) token before current cut = relationshipGuardedMetadata kind expected token before current cut
    bodyMetadata (groundingWriter {kind} {expected}) token before current cut = groundingGuardedMetadata kind expected token before current cut
    bodyMetadata (propagator {expected}) token before current cut = propagationGuardedMetadata expected token before current cut
    bodyMetadata (decayer {expected}) token before current cut = decayGuardedMetadata expected token before current cut
    bodyMetadata (documentRemover {expected}) token before current cut = clearGuardedMetadata expected token before current cut
    bodyMetadata defeater token before current cut = DefeatJournal.interruptedFrame token before current cut
    bodyMetadata sweeper token before current cut = SweepJournal.interruptedFrame token before current cut
    bodyMetadata sourceWriter token before current cut = sourceMetadata token before current cut
    bodyMetadata reviewer token before current cut = Reviewing.interruptedKeepsRegistration token before current cut ,
      Reviewing.interruptedKeepsCancellation token token before current cut
    bodyMetadata documentLoader token before current cut = DocumentEntry.interruptedMetadataFrame token before current cut



  module Creating = Binding.Creating library postgres using
    (Request; Call; Context; Result; needsInput; returned; ready; readProject; Environment
    ; Effect; Reply; Atomic; module X; module E; module Read; script; progress; Goal
    ; ReadyMeaning; completedReady; completedReadyResultAbsent; completedReadyReservation
    ; completedDecodedExistingUnchanged; readyRetrySameContext; transportReady; readyOperation
    ; matchesOriginalSettings; decode; completedReadyAdmission; completedKnownResult
    ; KnownResult; knownReady; knownCompleted; knownPolicyDialogue; Resumable; CompletedValue; Reserved
    ; completedGoal; converges; needsPolicy; preparedWrite; admittedWrite; dialogue)

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


    initialReady : ∀ requested before baseline scope →
      Creating.X.Completed (Creating.script requested) before baseline (Creating.ready scope) →
      Creating.decode requested ≡ inj₂ (Creating.Context.call scope) ×
      Creating.ReadyMeaning (Creating.Context.call scope) baseline scope
    initialReady requested before baseline scope prefix with Creating.completedReady requested before baseline scope prefix
    ... | call , decoded , known =
      trans decoded (cong inj₂ (sym (Creating.ReadyMeaning.actualCall known))) ,
      subst (λ actual → Creating.ReadyMeaning actual baseline scope) (sym (Creating.ReadyMeaning.actualCall known)) known

    relabelAdmission : ∀ first second token current → first ≡ second →
      (Σ (Replay.Read.ExecutionContext first token current) (λ actual → Replay.Read.admission first token current ≡ Replay.Read.admitted actual)) →
      Σ (Replay.Read.ExecutionContext second token current) (λ actual → Replay.Read.admission second token current ≡ Replay.Read.admitted actual)
    relabelAdmission first .first token current refl actual = actual

    initialAdmission : ∀ requested before baseline scope →
      Creating.X.Completed (Creating.script requested) before baseline (Creating.ready scope) →
      Σ (Replay.Read.ExecutionContext (Replay.writerName (bodyWriter scope))
        (Creating.Call.token (Creating.Context.call scope)) baseline) (λ actual →
        Replay.Read.admission (Replay.writerName (bodyWriter scope))
          (Creating.Call.token (Creating.Context.call scope)) baseline ≡ Replay.Read.admitted actual)
    initialAdmission requested before baseline scope prefix = relabelAdmission
      (Creating.Call.name (Creating.Context.call scope)) (Replay.writerName (bodyWriter scope))
      (Creating.Call.token (Creating.Context.call scope)) baseline (sym (bodyName scope))
      (Creating.completedReadyAdmission requested (Creating.Context.call scope) before baseline scope
        (proj₁ (initialReady requested before baseline scope prefix)) prefix)

    readbackAtCut : ∀ requested before baseline scope current →
      Creating.X.Completed (Creating.script requested) before baseline (Creating.ready scope) →
      Body.X.Interrupted scope (Body.script scope (bodyInput scope)) baseline current →
      Replay.Read.ResumableOrCompleted (Replay.writerName (bodyWriter scope))
        (Creating.Call.token (Creating.Context.call scope)) current
    readbackAtCut requested before baseline scope current prefix cut with initialAdmission requested before baseline scope prefix
    ... | actual , admitted = Replay.bodyReadback (bodyWriter scope)
      (Creating.Call.token (Creating.Context.call scope)) baseline current actual admitted cut

    readyAtCut : ∀ scope baseline current → Creating.ReadyMeaning (Creating.Context.call scope) baseline scope →
      Replay.MetadataFrame (Creating.Call.token (Creating.Context.call scope)) baseline current →
      Creating.ReadyMeaning (Creating.Context.call scope) current scope
    readyAtCut scope baseline current known (registration , cancellation) =
      Creating.transportReady (Creating.Context.call scope) baseline current scope
        (cong (λ rows → Project.Registered.binding token (proj₁ (proj₂ (proj₂ rows)))) registration)
        (cong (λ rows → Project.Registered.plan token (proj₂ (proj₂ (proj₂ rows)))) registration)
        cancellation known
      where token = Creating.Call.token (Creating.Context.call scope)

    reservationAtCut : ∀ call baseline current → Creating.Reserved call baseline →
      Step.registration current ≡ Step.registration baseline → Creating.Reserved call current
    reservationAtCut call baseline current (row , observed) registration = row ,
      trans (cong (λ rows → Registered.reservation (Creating.Call.token call) (proj₁ rows)) registration) observed

    allowedReadback : ∀ operation token current → Replay.Read.ResumableOrCompleted operation token current →
      Creating.Resumable (Creating.Read.answer token current) ⊎ Creating.CompletedValue (Creating.Read.answer token current)
    allowedReadback operation token current (inj₁ (entry , admitted)) with Replay.Read.admittedHasPending operation token current entry admitted
    ... | original , next , rows , observed = inj₁ (subst Creating.Resumable (sym observed) tt)
    allowedReadback operation token current (inj₂ (original , raw , completed)) =
      inj₂ (original , raw , Replay.Read.admissionCompletedAnswer operation token current original raw completed)

    completedAdmission : ∀ operation token current original raw → Replay.Read.ResumableOrCompleted operation token current →
      Creating.Read.answer token current ≡ Creating.Read.completed original raw →
      Replay.Read.admission operation token current ≡ Replay.Read.returned (Replay.Read.completed original raw)
    completedAdmission operation token current original raw (inj₁ (entry , admitted)) observed
      with Replay.Read.admittedHasPending operation token current entry admitted
    ... | binding , next , rows , pending = ⊥-elim (impossible (trans (sym pending) observed))
      where
      impossible : Replay.Read.pending binding next rows ≡ Replay.Read.completed original raw → ⊥
      impossible ()
    completedAdmission operation token current original raw (inj₂ (binding , value , completed)) observed
      with trans (sym (Replay.Read.admissionCompletedAnswer operation token current binding value completed)) observed
    ... | refl = completed

    readyDialogueGoal : ∀ requested call before baseline scope fault → Creating.decode requested ≡ inj₂ call →
      Creating.Goal requested before baseline (Creating.ready scope) →
      Creating.Goal requested before baseline (Creating.needsInput fault)
    readyDialogueGoal requested call before baseline scope fault decoded earlier rewrite decoded = proj₁ earlier , Creating.dialogue fault

    policyIsSweep : ∀ tool → Creating.needsPolicy tool ≡ true → tool ≡ Tools.sweepExpiredDefeated
    policyIsSweep Tools.insertBelief ()
    policyIsSweep Tools.deleteBelief ()
    policyIsSweep Tools.deleteProject ()
    policyIsSweep Tools.deletePattern ()
    policyIsSweep Tools.insertPattern ()
    policyIsSweep Tools.recordSupport ()
    policyIsSweep Tools.recordCause ()
    policyIsSweep Tools.recordDefeat ()
    policyIsSweep Tools.recordContradiction ()
    policyIsSweep Tools.getBelief ()
    policyIsSweep Tools.listBeliefs ()
    policyIsSweep Tools.listPatterns ()
    policyIsSweep Tools.getContradictions ()
    policyIsSweep Tools.decayAll ()
    policyIsSweep Tools.sweepExpiredDefeated refl = refl
    policyIsSweep Tools.queryRelevant ()
    policyIsSweep Tools.addEvidence ()
    policyIsSweep Tools.getEvidence ()
    policyIsSweep Tools.propagateFrom ()
    policyIsSweep Tools.queryIntervention ()
    policyIsSweep Tools.loadDocument ()
    policyIsSweep Tools.queryDocument ()
    policyIsSweep Tools.clearDocument ()
    policyIsSweep Tools.getLearningReview ()
    policyIsSweep Tools.learningCapabilities ()
    policyIsSweep Tools.getLessonAssessment ()
    policyIsSweep Tools.lessonAssessmentHistory ()
    policyIsSweep Tools.explainBelief ()
    policyIsSweep Tools.recordExperience ()
    policyIsSweep Tools.pendingExperiences ()
    policyIsSweep Tools.reviewExperience ()
    policyIsSweep Tools.getExperience ()
    policyIsSweep Tools.experienceHistory ()
    policyIsSweep Tools.queryLearningContext ()
    policyIsSweep Tools.reserveOperation ()
    policyIsSweep Tools.operationOutcome ()
    policyIsSweep Tools.cancelOperation ()

    policyBeforeUnchanged : ∀ requested before baseline scope current →
      Creating.X.Completed (Creating.script requested) before baseline (Creating.ready scope) →
      Body.X.Interrupted scope (Body.script scope (bodyInput scope)) baseline current →
      Creating.needsPolicy (Creating.Call.tool (Creating.Context.call scope)) ≡ true →
      Creating.Resumable (Creating.Read.answer (Creating.Call.token (Creating.Context.call scope)) current) → current ≡ baseline
    policyBeforeUnchanged requested before baseline scope@(Creating.preparedWrite (Creating.admittedWrite tool submitted writer invocation) original model raw)
      current prefix cut policy possible with policyIsSweep tool policy
    ... | refl with initialAdmission requested before baseline scope prefix
    ... | entry , admitted = Replay.pendingSweepUnchanged (Creating.Call.request (Creating.Context.call scope))
      (Creating.Call.token (Creating.Context.call scope)) baseline current entry admitted cut possible


    cachedCutMeaning : ∀ requested before baseline scope current original raw →
      Creating.X.Completed (Creating.script requested) before baseline (Creating.ready scope) →
      Body.X.Interrupted scope (Body.script scope (bodyInput scope)) baseline current →
      Creating.decode requested ≡ inj₂ (Creating.Context.call scope) →
      Replay.Read.ResumableOrCompleted (Replay.writerName (bodyWriter scope)) (Creating.Call.token (Creating.Context.call scope)) current →
      Creating.Read.answer (Creating.Call.token (Creating.Context.call scope)) current ≡ Creating.Read.completed original raw →
      Meaning requested before current (returned (Creating.Read.completed original raw))
    cachedCutMeaning requested before baseline scope current original raw prefix cut decoded readState observed
      with Replay.bodyReplay (bodyWriter scope) (Creating.Call.token (Creating.Context.call scope)) baseline current original raw
        (Creating.completedReadyResultAbsent requested (Creating.Context.call scope) before baseline scope decoded prefix)
        (Replay.Read.admissionCompletedLookup (Replay.writerName (bodyWriter scope)) (Creating.Call.token (Creating.Context.call scope))
          current original raw (completedAdmission (Replay.writerName (bodyWriter scope)) (Creating.Call.token (Creating.Context.call scope))
            current original raw readState observed))
        (completedAdmission (Replay.writerName (bodyWriter scope)) (Creating.Call.token (Creating.Context.call scope))
          current original raw readState observed) cut
    ... | actual , completedBody , same = cachedBusinessOutcome baseline scope actual original raw
      (Creating.completedGoal requested before baseline (Creating.ready scope) prefix)
      (Body.converges scope (bodyInput scope) baseline current current actual cut completedBody) same observed

    policyCutMeaning : ∀ requested before baseline scope current fault →
      Creating.X.Completed (Creating.script requested) before baseline (Creating.ready scope) →
      Body.X.Interrupted scope (Body.script scope (bodyInput scope)) baseline current →
      Creating.decode requested ≡ inj₂ (Creating.Context.call scope) →
      Creating.needsPolicy (Creating.Call.tool (Creating.Context.call scope)) ≡ true →
      Creating.Resumable (Creating.Read.answer (Creating.Call.token (Creating.Context.call scope)) current) →
      Meaning requested before current (needsInput fault)
    policyCutMeaning requested before baseline scope current fault prefix cut decoded policy possible
      with policyBeforeUnchanged requested before baseline scope current prefix cut policy possible
    ... | refl = preparationDialogue fault (readyDialogueGoal requested (Creating.Context.call scope) before baseline scope fault decoded
      (Creating.completedGoal requested before baseline (Creating.ready scope) prefix))

    joinKnown : ∀ requested before baseline scope current after reply →
      Creating.X.Completed (Creating.script requested) before baseline (Creating.ready scope) →
      Body.X.Interrupted scope (Body.script scope (bodyInput scope)) baseline current →
      Creating.decode requested ≡ inj₂ (Creating.Context.call scope) →
      Creating.Reserved (Creating.Context.call scope) current → Creating.ReadyMeaning (Creating.Context.call scope) current scope →
      Replay.Read.ResumableOrCompleted (Replay.writerName (bodyWriter scope)) (Creating.Call.token (Creating.Context.call scope)) current →
      X.Completed (script requested) current after reply → Meaning requested before after reply
    joinKnown requested before baseline scope current after reply prefix cut decoded reserved known readState retry
      with splitPrefixRun (Creating.script requested) current after reply (X.Completed.returned retry) (X.Completed.changes retry)
    ... | middle , prepared , prefixRetry , remainder
      with Creating.completedKnownResult requested (Creating.Context.call scope) current scope middle prepared decoded reserved known
        (allowedReadback (Replay.writerName (bodyWriter scope)) (Creating.Call.token (Creating.Context.call scope)) current readState) prefixRetry
    ... | Creating.knownReady nextScope
      with Creating.readyRetrySameContext requested (Creating.Context.call scope) current middle scope nextScope decoded known prefixRetry
    ... | refl , refl with remainder
    ... | X.completed events execution physical
      with unliftBodyRun scope (Body.script scope (bodyInput scope)) current after reply execution physical
    ... | actual , refl , completedBody = businessOutcome baseline scope actual
      (Creating.completedGoal requested before baseline (Creating.ready scope) prefix)
      (Body.converges scope (bodyInput scope) baseline current after actual cut completedBody)
    joinKnown requested before baseline scope current after reply prefix cut decoded reserved known readState retry
      | middle , prepared , prefixRetry , remainder | Creating.knownCompleted original raw observed
      with Creating.completedDecodedExistingUnchanged requested (Creating.Context.call scope) current middle
        (Creating.returned (Creating.Read.completed original raw)) (Creating.Context.original scope) (Creating.Context.raw scope)
        decoded (Creating.ReadyMeaning.boundRequest known) (Creating.ReadyMeaning.savedPlan known) prefixRetry
    ... | refl with remainder
    ... | X.completed [] (E.returned _) (X.unchanged _) = cachedCutMeaning requested before baseline scope current original raw
      prefix cut decoded readState observed
    joinKnown requested before baseline scope current after reply prefix cut decoded reserved known readState retry
      | middle , prepared , prefixRetry , remainder | Creating.knownPolicyDialogue fault policy possible
      with Creating.completedDecodedExistingUnchanged requested (Creating.Context.call scope) current middle
        (Creating.needsInput fault) (Creating.Context.original scope) (Creating.Context.raw scope)
        decoded (Creating.ReadyMeaning.boundRequest known) (Creating.ReadyMeaning.savedPlan known) prefixRetry
    ... | refl with remainder
    ... | X.completed [] (E.returned _) (X.unchanged _) = policyCutMeaning requested before baseline scope current fault
      prefix cut decoded policy possible

    joinPublishing : ∀ requested before baseline scope current after reply →
      Creating.X.Completed (Creating.script requested) before baseline (Creating.ready scope) →
      Body.X.Interrupted scope (Body.script scope (bodyInput scope)) baseline current →
      X.Completed (script requested) current after reply → Meaning requested before after reply
    joinPublishing requested before baseline scope current after reply prefix cut retry =
      joinKnown requested before baseline scope current after reply prefix cut (proj₁ original)
        (reservationAtCut (Creating.Context.call scope) baseline current
          (Creating.completedReadyReservation requested (Creating.Context.call scope) before baseline scope (proj₁ original) prefix)
          (proj₁ metadata))
        (readyAtCut scope baseline current (proj₂ original) metadata)
        (readbackAtCut requested before baseline scope current prefix cut) retry
      where
      original = initialReady requested before baseline scope prefix
      metadata = Replay.bodyMetadata (bodyWriter scope) (Creating.Call.token (Creating.Context.call scope)) baseline current cut

    converges : ∀ requested before current after reply → X.Interrupted (script requested) before current →
      X.Completed (script requested) current after reply → Meaning requested before after reply
    converges requested before current after reply cut retry
      with splitInterruptedPrefix (Creating.script requested) before current cut
    ... | preparing prefixCut with splitPrefixRun (Creating.script requested) current after reply
      (X.Completed.returned retry) (X.Completed.changes retry)
    ... | baseline , prepared , prefixRetry , remainder = prefixThenBodyMeaning requested before baseline after prepared reply
      (Creating.converges requested before current baseline prepared prefixCut prefixRetry) remainder
    converges requested before current after reply cut retry | publishing baseline scope prefix bodyCut =
      joinPublishing requested before baseline scope current after reply prefix bodyCut retry

    operation : Recovery.RecoverableFor Store.World Creating.Request Response Meaning
    operation = record { Effect = Effect; Reply = Reply; script = script; Atomic = Atomic; converges = converges; progress = progress }

    Succeeded : Response → Set
    Succeeded (needsInput _) = ⊥
    Succeeded (returned (Creating.Read.completed _ _)) = ⊤
    Succeeded (returned _) = ⊥
    Succeeded (executed scope reply) = Success (bodyKind scope) reply
