{-# OPTIONS --safe #-}
-- Concrete operation kinds determine their inputs, replies and business
-- goals. There is no caller-selected goal, script or physical relation here.
module Mimir.PublicOperationCatalogue where

open import Data.Bool using (Bool)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Float.Base using (Float)
open import Data.Integer using (ℤ)
open import Data.List using (List; [])
import Data.Maybe
open import Data.Nat using (ℕ; zero; suc; s≤s; z≤n)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
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
  (allocateOwner : ℕ → Store.World → IndependentIntent.Allocation) where
  module Admit = Binding.Decode library
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
  module BeliefRemoval = DeleteBelief.Registered library databaseSum calculator
  module Grounding kind = Ground.Registered kind library databaseSum calculator
  module Propagate = Propagation.Registered format library databaseSum calculator
  module Decaying = Decay.Registered library databaseSum
  module DocumentRemoval = Clear.Registered library databaseSum calculator
  module IndependentWrite = Independent.Registered format library databaseSum calculator allocateOwner
  module IndependentPublic = IndependentWrite.Public configuration
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

  module BeliefRemovalFrame = Binding.AdmittedStep ℕ BeliefRemoval.B.Diagnostic (λ token → token) BeliefRemoval.key
    BeliefRemoval.distinct BeliefRemoval.decide BeliefRemoval.keepsJournal BeliefRemoval.admit
  module BeliefRemovalGuard expected = Admit.Guarded (Binding.advertised Tools.deleteBelief) expected BeliefRemoval.operation
    (λ token → BeliefRemovalFrame.existingBindingSurvives token token)

  module GroundingFrame kind = Binding.AdmittedStep ℕ (Grounding.B.Diagnostic kind) (λ token → token) (Grounding.key kind)
    (Grounding.distinct kind) (Grounding.decide kind) (Grounding.keepsJournal kind) (Grounding.admit kind)
  groundingSource : Ground.Kind → Binding.Source
  groundingSource Ground.addition = Binding.advertised Tools.addEvidence
  groundingSource Ground.removal = Binding.evidenceRemoval
  module GroundingGuard kind expected = Admit.Guarded (groundingSource kind) expected (Grounding.operation kind)
    (λ token → GroundingFrame.existingBindingSurvives kind token token)

  module PropagationFrame = Binding.AdmittedStep ℕ Propagate.B.Diagnostic (λ token → token) Propagate.key
    Propagate.distinct Propagate.decide Propagate.keepsJournal Propagate.admit
  module PropagationGuard expected = Admit.Guarded (Binding.advertised Tools.propagateFrom) expected Propagate.operation
    (λ token → PropagationFrame.existingBindingSurvives token token)
  module DecayFrame = Binding.AdmittedStep ℕ Decaying.B.Diagnostic (λ token → token) Decaying.key
    Decaying.distinct Decaying.decide Decaying.keepsJournal Decaying.admit
  module DecayGuard expected = Admit.Guarded (Binding.advertised Tools.decayAll) expected Decaying.operation
    (λ token → DecayFrame.existingBindingSurvives token token)
  module ClearFrame = Binding.AdmittedStep ℕ DocumentRemoval.B.G.Diagnostic (λ token → token) DocumentRemoval.key
    DocumentRemoval.distinct DocumentRemoval.decide DocumentRemoval.keepsJournal DocumentRemoval.admit
  module ClearGuard expected = Admit.Guarded (Binding.advertised Tools.clearDocument) expected DocumentRemoval.operation
    (λ token → ClearFrame.existingBindingSurvives token token)

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
  module IndependentGuard expected proof = Admit.Guarded (Binding.advertised Tools.insertBelief) expected
    (IndependentPublic.toRecoverable proof)
    (λ token → IndependentFrame.existingBindingSurvives (IndependentPublic.script token) token)

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
  Result (independentWrite expected) = IndependentGuard.Result expected IndependentPublic.fullOperation
  Result (patternRemoval expected) = PatternRemovalGuard.Result expected
  Result (beliefRemoval expected) = BeliefRemovalGuard.Result expected
  Result (relationship kind expected) = RelationshipGuard.Result kind expected
  Result (grounding kind expected) = GroundingGuard.Result kind expected
  Result (propagation expected) = PropagationGuard.Result expected
  Result (decay expected) = DecayGuard.Result expected
  Result (documentRemoval expected) = ClearGuard.Result expected

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
  Goal (independentWrite expected) = IndependentGuard.Goal expected IndependentPublic.fullOperation
  Goal (patternRemoval expected) = PatternRemovalGuard.Goal expected
  Goal (beliefRemoval expected) = BeliefRemovalGuard.Goal expected
  Goal (relationship kind expected) = RelationshipGuard.Goal kind expected
  Goal (grounding kind expected) = GroundingGuard.Goal kind expected
  Goal (propagation expected) = PropagationGuard.Goal expected
  Goal (decay expected) = DecayGuard.Goal expected
  Goal (documentRemoval expected) = ClearGuard.Goal expected

  -- Observed operations require their complete certificate at assembly.
  -- There is no generic recoverability constructor for these cases.
  Certificate : Kind → Set₁
  Certificate (retrieval request) = Retrieval.Operation
  Certificate (context request) = LearningContext.Operation
  Certificate (documentQuery request) = DocumentQuery.Operation
  Certificate (independentWrite expected) = IndependentPublic.Operation
  Certificate kind = Recovery.RecoverableFor Store.World (Input kind) (Result kind) (Goal kind)

  certificate : (kind : Kind) → Certificate kind
  certificate (basic request) = BasicFixed.operation request
  certificate (experiences request) = ExperienceFixed.operation request
  certificate (assessments request) = AssessmentFixed.operation request
  certificate (intervention request) = InterventionFixed.operation request
  certificate (retrieval request) = Retrieval.operation
  certificate (context request) = LearningContext.operation
  certificate (documentQuery request) = DocumentQuery.fullOperation
  certificate (projectRemoval project) = ProjectSelected.operation project
  certificate (correction diagnostic) = Refusal.operation diagnostic
  certificate (patternWrite expected) = PatternGuard.operation expected
  certificate (independentWrite expected) = IndependentPublic.fullOperation
  certificate (patternRemoval expected) = PatternRemovalGuard.operation expected
  certificate (beliefRemoval expected) = BeliefRemovalGuard.operation expected
  certificate (relationship kind expected) = RelationshipGuard.operation kind expected
  certificate (grounding kind expected) = GroundingGuard.operation kind expected
  certificate (propagation expected) = PropagationGuard.operation expected
  certificate (decay expected) = DecayGuard.operation expected
  certificate (documentRemoval expected) = ClearGuard.operation expected

  executable : (kind : Kind) → Certificate kind →
    Recovery.RecoverableFor Store.World (Input kind) (Result kind) (Goal kind)
  executable (retrieval request) proof = Fixed.operation (Retrieval.toRecoverable proof) request
  executable (context request) proof = Fixed.operation (LearningContext.toRecoverable proof) request
  executable (documentQuery request) proof = Fixed.operation (DocumentQuery.toRecoverable proof) request
  executable (independentWrite expected) proof = IndependentGuard.operation expected proof
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
