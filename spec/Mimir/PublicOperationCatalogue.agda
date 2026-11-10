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
  module Relationship kind = Edges.Registered library (Encoding.Formatting.uuidText format) kind
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
      (ExecutionContext; admission; admissionCompletedLookup; admitted; completed; returned; undeclaredAbsent)
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

  module Creating = Binding.Creating library postgres using
    (Request; Call; Context; Result; needsInput; returned; ready; readProject; Environment
    ; Effect; Reply; Atomic; module X; module E; module Read; script; progress; Goal
    ; ReadyMeaning; completedReady; completedReadyResultAbsent; completedReadyReservation
    ; completedDecodedExistingUnchanged; readyRetrySameContext; transportReady; readyOperation
    ; matchesOriginalSettings; decode; completedReadyAdmission; completedKnownResult
    ; KnownResult; knownReady; knownCompleted; knownPolicyDialogue; Resumable; CompletedValue; Reserved
    ; completedGoal; converges; needsPolicy; preparedWrite; admittedWrite; dialogue)
