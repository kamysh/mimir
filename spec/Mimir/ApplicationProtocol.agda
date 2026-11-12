{-# OPTIONS --safe #-}
-- Concrete dispatch for every public application request. Subprotocols retain
-- their typed effects, failures and commit receipts. Retrieval is a transition
-- system because concurrent data can grow; no arbitrary traversal fuel is used.
module Mimir.ApplicationProtocol where

open import Data.Bool using (Bool; true; false)
open import Data.Float.Base using (Float)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁)
import Data.String
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Mimir.Text using (Text)
open import Mimir.UUIDGroups using (UUID; _≟UUID_)
open import Mimir.Binary64 using (Number)
import Mimir.ApplicationFloat as Numeric
import Mimir.GraphNumerics as GraphNumerics
import Mimir.PublicRequest as Public
import Mimir.GraphMutationProtocol as Mutation
import Mimir.BeliefEmbedding as BeliefEmbedding
import Mimir.GraphReadProtocol as Read
import Mimir.GraphRecords as Records
import Mimir.GraphWrites as Writes
import Mimir.ReviewSchema as Relations
import Mimir.LearningRecompute as Recompute
import Mimir.PosteriorComputation as Posterior
import Mimir.GraphDeletion as Deletion
import Mimir.ProjectDeletion as Project
import Mimir.InferenceProtocol as Inference
import Mimir.GroundingPublication as Ground
import Mimir.EvidenceRead as Evidence
import Mimir.DocumentLoading as Documents
import Mimir.DocumentStore as DocumentStore
import Mimir.DocumentQuery as DocumentQuery
import Mimir.RetrievalProtocol as Retrieval
import Mimir.RetrievalRanking as Ranking
import Mimir.LearningContextProtocol as Context
import Mimir.LearningOperations as Learning
import Mimir.LearningStore as LearningStore
import Mimir.ReviewObservation as Observation
import Mimir.LearningQueryProtocol as Query
import Mimir.ExperienceRead as ExperienceRead
import Mimir.AssessmentRead as AssessmentRead
import Mimir.LearningHistory as LearningHistory
import Mimir.IndependentProvenance as Origin
import Mimir.Validation as Validation
import Mimir.LearningCandidates as Candidates
import Mimir.LearningCapabilities as Capabilities
import Mimir.CandidateGraph as Graph
import Mimir.McpEnvelope as Envelope
import Mimir.StructuredValue as JSON
import Mimir.ApplicationStore as Store
import Mimir.Effects as Effects
import Mimir.DatabaseTransaction as DB
import Mimir.Recovery as Recovery

record Environment : Set₁ where
  field
    database dimension : ℕ
    embeddingsEnabled : Bool
    retirementGraceHours : Maybe Float
    f32 : Ranking.F32
    unicode : Ranking.Unicode
    databaseTextBefore : Text → Text → Bool
    now : ℤ
    candidateClock : Candidates.Candidate → ℤ
    -- Identities are supplied by PostgreSQL. The index selects a chunk's
    -- supplied identity; it is not itself an identity or an ordering of UUIDs.
    candidateIdentity : Candidates.Candidate → UUID
    chunkIdentity : ℕ → UUID
    calculation : Posterior.Calculation

module Run (environment : Environment) where
  open Environment environment
  module Delete = Deletion.Operation database calculation
  module Sweep = Delete.Batch
  module RelationRecovery (command : Mutation.Statement) = Mutation.StatementRecovery command
  module DefeatRecovery (from to : UUID) (weight : Number) = Mutation.DefeatRecovery from to weight
  module DeleteRecovery (kind : Deletion.Kind) (id : UUID) = Delete.T.RecoveryPlan (Delete.delete kind id)
  module Forget = Project.Operation database
  module Standalone (project : Text) = Project.Standalone database project
  module Grounding = Ground.Operation database calculation
  module GroundRecovery (request : Ground.Request) = Grounding.T.RecoveryPlan (Grounding.plan request)
  module Document = Documents.Operations database dimension
  module DocumentClearRecovery (path : Text) = Document.ClearRecovery path
  module DocumentReplaceRecovery (path : Text) (chunks : List DocumentStore.Chunk) (vectors : List Store.Vector) =
    Document.ReplaceRecovery path chunks vectors
  module Learn (q : Learning.Request) = Learning.Protocol database q candidateClock now candidateIdentity calculation
  module Retrieve = Retrieval.Run f32 unicode
  module LearningContext = Context.Run f32 unicode databaseTextBefore

  data Result : Set where
    mutated : Mutation.Result → Result
    readResult : Read.Result → Result
    deleted : Delete.T.Outcome → Result
    forgotten : Forget.Result → Result
    inferred : Inference.Result → Result
    swept : Sweep.S.Outcome → Result
    grounded : Grounding.T.Outcome → Result
    invalidGrounding : Result
    evidenceResult : Text ⊎ List Evidence.Reference → Result
    relevantResult : List Graph.BeliefValues → Result
    groundedResult : Text ⊎ List Evidence.Grounded → Result
    documentResult : Document.Result → Result
    documentQueryResult : DocumentQuery.Result → Result
    learned : (q : Learning.Request) → Learn.Outcome q → Result
    learningQueryResult : Query.Result → Result
    contextResult : Context.Output → Result
    capabilitiesResult : Capabilities.Capabilities → Result
    failed : Text → Result
    needsDecision : Text → Text → Result
    invalidRequestIdentity : Result
    invalidContext invalidAssessment : Result

  record PatternPublished (situation approach : Text) (success : Float) (project : Maybe Text)
    (patternValue : Graph.PatternValues) (before after : Store.World) : Set where
    field
      patternWasAbsent : Records.getPattern (Graph.PatternValues.identity patternValue) (Store.patterns (Store.nodes before)) ≡ nothing
      patternStored : Records.getPattern (Graph.PatternValues.identity patternValue) (Store.patterns (Store.nodes after)) ≡ just patternValue
      situationMatches : Graph.PatternValues.situation patternValue ≡ situation
      approachMatches : Graph.PatternValues.approach patternValue ≡ approach
      projectMatches : Graph.PatternValues.project patternValue ≡ project
      successMatches : Graph.PatternValues.successRate patternValue ≡ success

  record BeliefPublished (proposal : BeliefEmbedding.Draft)
    (material : BeliefEmbedding.Prepared) (belief : Graph.BeliefValues)
    (before after : Store.World) : Set where
    field
      supportWasIndexed : BeliefEmbedding.Prepared.supportingPassage material ∈ Store.World.chunks before
      supportRetained : BeliefEmbedding.Prepared.supportingPassage material ∈ Store.World.chunks after
      beliefWasAbsent : Ranking.lookup (Graph.BeliefValues.identity belief) (Store.beliefs before) ≡ nothing
      beliefStored : Ranking.lookup (Graph.BeliefValues.identity belief) (Store.beliefs after) ≡ just belief
      vectorStored : (Graph.BeliefValues.identity belief , BeliefEmbedding.vector material) ∈ Store.World.beliefVectors after
      sourceStored : Σ Store.Ground (λ source → source ∈ Store.World.grounds after ×
        Store.Ground.belief source ≡ Graph.BeliefValues.identity belief ×
        Store.Ground.chunk source ≡ DocumentStore.Chunk.identity (BeliefEmbedding.Prepared.supportingPassage material))
      contentMatches : Graph.BeliefValues.content belief ≡ BeliefEmbedding.Draft.content proposal
      projectMatches : Graph.BeliefValues.project belief ≡ BeliefEmbedding.Draft.project proposal
      memoryMatches : Graph.BeliefValues.memory belief ≡ BeliefEmbedding.Draft.memory proposal
      probabilityMatches : Graph.BeliefValues.probability belief ≡ BeliefEmbedding.Draft.probability proposal
      confidenceMatches : Graph.BeliefValues.confidence belief ≡ BeliefEmbedding.Draft.confidence proposal

  -- Capability discovery is a pure operation: no store effect is issued and
  -- its retry leaves the observable world unchanged.
  capabilitySucceeded : Result → Set
  capabilitySucceeded result = result ≡ capabilitiesResult (Capabilities.capabilities 2 1 true true true true)
  module Capability = Recovery Store.World ⊥ Result (λ _ → ⊤)
    (λ ()) (λ _ ()) (λ before after → before ≡ after)
    (λ _ _ → Store.World) (λ _ _ world → world) (λ _ world → world) capabilitySucceeded (λ _ → ⊤)
  module CapabilityProof = Capability.Pure
    (λ (_ : ⊤) → capabilitiesResult (Capabilities.capabilities 2 1 true true true true))
  capabilityOperation : Capability.Recoverable ⊤
  capabilityOperation = CapabilityProof.pure

  readSucceeded : Read.Result → Set
  readSucceeded (Read.failed _) = ⊥
  readSucceeded Read.invalidPage = ⊥
  readSucceeded Read.missingBelief = ⊥
  readSucceeded Read.invalidProvenance = ⊥
  readSucceeded _ = ⊤

  module ReadRecovery = Recovery Store.World Read.Effect Read.Result (λ _ → ⊤) Read.Reply
    (λ before effect reply after → after ≡ before)
    (λ before after → after ≡ before)
    (λ _ _ → Store.World) (λ _ _ world → world)
    (λ _ world → world) readSucceeded (λ _ → ⊤)
  module ReadProof = ReadRecovery.ReadOnly (λ _ _ _ _ same → same)
    (λ _ _ same → same) (λ _ _ → refl)
  readOperation : ReadRecovery.Recoverable Read.Request
  readOperation = ReadProof.readOnly Read.start

  querySucceeded : Query.Result → Set
  querySucceeded (Query.failed _) = ⊥
  querySucceeded (Query.invalidRequest _) = ⊥
  querySucceeded (Query.invalidTarget _) = ⊥
  querySucceeded (Query.pendingResult ExperienceRead.invalidLimit) = ⊥
  querySucceeded (Query.historyResult LearningHistory.inconsistentHistory) = ⊥
  querySucceeded (Query.scoreResult AssessmentRead.missingScope) = ⊥
  querySucceeded (Query.scoreResult (AssessmentRead.invalidTarget _)) = ⊥
  querySucceeded (Query.assessmentHistoryResult AssessmentRead.invalidPage) = ⊥
  querySucceeded (Query.assessmentHistoryResult AssessmentRead.missingProject) = ⊥
  querySucceeded (Query.assessmentHistoryResult AssessmentRead.invalidStoredHistory) = ⊥
  querySucceeded _ = ⊤
  module QueryRecovery = Recovery Store.World Query.Effect Query.Result (λ _ → ⊤) Query.Reply
    (λ before effect reply after → after ≡ before)
    (λ before after → after ≡ before)
    (λ _ _ → Store.World) (λ _ _ world → world)
    (λ _ world → world) querySucceeded (λ _ → ⊤)
  module QueryProof = QueryRecovery.ReadOnly (λ _ _ _ _ same → same)
    (λ _ _ same → same) (λ _ _ → refl)
  queryOperation : QueryRecovery.Recoverable Query.Request
  queryOperation = QueryProof.readOnly Query.start

  inferenceQuerySucceeded : Inference.Result → Set
  inferenceQuerySucceeded (Inference.projected _ _) = ⊤
  inferenceQuerySucceeded (Inference.pairs _) = ⊤
  inferenceQuerySucceeded _ = ⊥

  module InferenceQueryRecovery = Recovery Store.World Inference.ReadEffect Inference.Result
    (λ _ → ⊤) Inference.ReadReply
    (λ before effect reply after → after ≡ before)
    (λ before after → after ≡ before)
    (λ _ _ → Store.World) (λ _ _ storeValue → storeValue)
    (λ _ storeValue → storeValue) inferenceQuerySucceeded (λ _ → ⊤)
  module InferenceQueryProof = InferenceQueryRecovery.ReadOnly
    (λ _ _ _ _ same → same) (λ _ _ same → same) (λ _ _ → refl)
  inferenceQueryOperation : InferenceQueryRecovery.Recoverable Inference.ReadRequest
  inferenceQueryOperation = InferenceQueryProof.readOnly Inference.readStart

  module InferencePreparationRecovery = Recovery Store.World Inference.ReadEffect Inference.Preparation
    (λ _ → ⊤) Inference.ReadReply (λ before _ _ after → after ≡ before)
    (λ before after → after ≡ before) (λ _ _ → Store.World)
    (λ _ _ storeValue → storeValue) (λ _ storeValue → storeValue) (λ _ → ⊤) (λ _ → ⊤)
  module InferencePreparationProof = InferencePreparationRecovery.ReadOnly
    (λ _ _ _ _ same → same) (λ _ _ same → same) (λ _ _ → refl)
  inferencePreparationOperation : InferencePreparationRecovery.Recoverable Inference.Request
  inferencePreparationOperation = InferencePreparationProof.readOnly Inference.prepareRequest

  module LearningRecovery (request : Learning.Request) where
    module L = Learn request

    PreparationRead : Store.World → (effect : L.PreparationEffect) → L.PreparationReply effect → Set
    PreparationRead before (L.stage (L.T.read tx , witness)) (inj₂ observed) =
      observed ≡ Store.World.learning before
    PreparationRead before effect reply = ⊤

    PreparationAtomic : Store.World → (effect : L.PreparationEffect) →
      L.PreparationReply effect → Store.World → Set
    PreparationAtomic before effect reply after = (after ≡ before) × PreparationRead before effect reply

    module P = Recovery Store.World L.PreparationEffect L.PreparationResult
      (λ _ → ⊤) L.PreparationReply PreparationAtomic
      (λ before after → after ≡ before) (λ _ _ → Store.World)
      (λ _ _ world → world) (λ _ world → world) (λ _ → ⊤) (λ _ → ⊤)

    module PreparationProof = P.ReadOnly
      (λ _ _ _ _ proof → proj₁ proof) (λ _ _ same → same) (λ _ _ → refl)

    preparation : P.Recoverable ⊤
    preparation = PreparationProof.readOnly (λ _ → L.prepare)

    succeeded : L.Outcome → Set
    succeeded (L.transacted (L.T.applied _)) = ⊤
    succeeded (L.transacted (L.T.replayed _ _)) = ⊤
    succeeded _ = ⊥

    module Commit (tx : L.T.Transaction) (proposed : LearningStore.World)
      (value : Observation.Snapshot) where
      intended : Store.World → Store.World
      intended before = record before { learning = proposed }

      Atomic : Store.World → ⊤ → L.T.CommitReply → Store.World → Set
      Atomic before tt reply after = DB.Atomic before (intended before) (L.T.receipt reply) after

      answer : L.T.CommitReply → L.Outcome
      answer reply = L.transacted (L.T.committedOutcome value reply)

      module R = Recovery Store.World ⊤ L.Outcome (λ _ → ⊤) (λ _ → L.T.CommitReply)
        Atomic (λ before after → after ≡ before) (λ _ _ → Store.World)
        (λ _ _ world → world) (λ _ world → world) succeeded (λ _ → ⊤)

      success : (input : ⊤) → ∀ before reply after → Atomic before tt reply after →
        succeeded (answer reply) → (index : ⊤) → after ≡ intended before
      success input before L.T.committed after DB.committedAll proof index = refl
      success input before (L.T.aborted detail) after atomic () index

      unchangedFailure : ∀ before reply after → Atomic before tt reply after →
        ¬ succeeded (answer reply) → after ≡ before
      unchangedFailure before L.T.committed after atomic notSuccessful = ⊥-elim (notSuccessful tt)
      unchangedFailure before (L.T.aborted detail) after DB.abortedNone notSuccessful = refl

      call : R.FinalCall ⊤
      call = record
        { effect = λ _ → tt ; answer = λ _ → answer
        ; expected = λ _ before _ → intended before
        ; success = success ; failureUnchanged = λ _ → unchangedFailure
        ; crashUnchanged = λ _ _ same → same
        }
      module Certified = R.FinalPublication call
      recovery : R.Recoverable ⊤
      recovery = Certified.finalPublication

  module PosteriorRecovery (writes : Posterior.State) (result : Inference.Result)
    (successful : Inference.Successful result) where
    intended : Store.World → Store.World
    intended before = Store.setNodes (Recompute.apply writes (Store.nodes before)) before

    Atomic : Store.World → ⊤ → Text ⊎ DB.Receipt → Store.World → Set
    Atomic before tt (inj₁ detail) after = after ≡ before
    Atomic before tt (inj₂ receipt) after = DB.Atomic before (intended before) receipt after

    answer : Text ⊎ DB.Receipt → Inference.Result
    answer (inj₁ detail) = Inference.failed detail
    answer (inj₂ DB.aborted) = Inference.publicationAborted
    answer (inj₂ DB.committed) = result

    module R = Recovery Store.World ⊤ Inference.Result (λ _ → ⊤) (λ _ → Text ⊎ DB.Receipt)
      Atomic (λ before after → after ≡ before) (λ _ _ → Store.World)
      (λ _ _ storeValue → storeValue) (λ _ storeValue → storeValue)
      Inference.Successful (λ _ → ⊤)

    success : (input : ⊤) → ∀ before reply after → Atomic before tt reply after →
      Inference.Successful (answer reply) → (index : ⊤) → after ≡ intended before
    success input before (inj₁ detail) after atomic () index
    success input before (inj₂ DB.aborted) after atomic () index
    success input before (inj₂ DB.committed) after DB.committedAll proof index = refl

    failedUnchanged : ∀ before reply after → Atomic before tt reply after →
      ¬ Inference.Successful (answer reply) → after ≡ before
    failedUnchanged before (inj₁ detail) after same notSuccessful = same
    failedUnchanged before (inj₂ DB.aborted) after DB.abortedNone notSuccessful = refl
    failedUnchanged before (inj₂ DB.committed) after atomic notSuccessful = ⊥-elim (notSuccessful successful)

    call : R.FinalCall ⊤
    call = record
      { effect = λ _ → tt
      ; answer = λ _ → answer
      ; expected = λ _ before _ → intended before
      ; success = success
      ; failureUnchanged = λ _ → failedUnchanged
      ; crashUnchanged = λ _ _ same → same
      }
    module Certified = R.FinalPublication call
    recovery : R.Recoverable ⊤
    recovery = Certified.finalPublication

  data EvidenceRequest : Set where
    oneEvidence : UUID → EvidenceRequest

  evidenceProgram : EvidenceRequest → Evidence.E.Script Result
  evidenceProgram (oneEvidence belief) = Evidence.E._>>=_ (Evidence.one belief nothing)
    (λ result → Evidence.E.done (evidenceResult result))

  evidenceSucceeded : Result → Set
  evidenceSucceeded (evidenceResult (inj₂ _)) = ⊤
  evidenceSucceeded _ = ⊥
  module EvidenceRecovery = Recovery Store.World Evidence.Effect Result (λ _ → ⊤) Evidence.Reply
    (λ before effect reply after → after ≡ before)
    (λ before after → after ≡ before)
    (λ _ _ → Store.World) (λ _ _ world → world)
    (λ _ world → world) evidenceSucceeded (λ _ → ⊤)
  module EvidenceProof = EvidenceRecovery.ReadOnly (λ _ _ _ _ same → same)
    (λ _ _ same → same) (λ _ _ → refl)
  evidenceOperation : EvidenceRecovery.Recoverable EvidenceRequest
  evidenceOperation = EvidenceProof.readOnly evidenceProgram

  documentSearchSucceeded : DocumentQuery.Result → Set
  documentSearchSucceeded (DocumentQuery.found _) = ⊤
  documentSearchSucceeded _ = ⊥
  module DocumentSearchRecovery = Recovery Store.World DocumentQuery.Effect DocumentQuery.Result
    (λ _ → ⊤) DocumentQuery.Reply
    (λ before effect reply after → after ≡ before)
    (λ before after → after ≡ before)
    (λ _ _ → Store.World) (λ _ _ world → world)
    (λ _ world → world) documentSearchSucceeded (λ _ → ⊤)
  module DocumentSearchProof = DocumentSearchRecovery.ReadOnly (λ _ _ _ _ same → same)
    (λ _ _ same → same) (λ _ _ → refl)
  DocumentSearch = Text × Maybe Text × Maybe ℕ
  documentSearchOperation : DocumentSearchRecovery.Recoverable DocumentSearch
  documentSearchOperation = DocumentSearchProof.readOnly
    (λ { (query , project , limit) → DocumentQuery.start embeddingsEnabled query limit project })

  PatternInput = Text × Text × Float × Maybe Text
  -- The second component is the returned value, not a database column. The
  -- observation follows its opaque UUID back to the actual stored pattern.
  PatternWorld = Store.World × Maybe Graph.PatternValues

  patternView : Maybe Graph.PatternValues → Maybe PatternInput
  patternView nothing = nothing
  patternView (just patternValue) = just
    (Graph.PatternValues.situation patternValue , Graph.PatternValues.approach patternValue ,
      Graph.PatternValues.successRate patternValue , Graph.PatternValues.project patternValue)

  patternObservation : PatternWorld → Maybe PatternInput
  patternObservation (store , nothing) = nothing
  patternObservation (store , just returned) = patternView
    (Records.getPattern (Graph.PatternValues.identity returned) (Store.patterns (Store.nodes store)))

  finishPattern : Mutation.Result → PatternWorld → PatternWorld
  finishPattern (Mutation.insertedPattern patternValue) (store , previous) = store , just patternValue
  finishPattern _ world = world

  patternSucceeded : Mutation.Result → Set
  patternSucceeded (Mutation.insertedPattern _) = ⊤
  patternSucceeded _ = ⊥

  PatternAtomic : PatternWorld → (effect : Mutation.Effect) → Mutation.Reply effect → PatternWorld → Set
  PatternAtomic (before , previous) (Mutation.createPattern situation approach success project) (inj₂ patternValue) (after , last) =
    (last ≡ previous) × PatternPublished situation approach success project patternValue before after
  PatternAtomic before _ _ after = after ≡ before

  module PatternRecovery = Recovery PatternWorld Mutation.Effect Mutation.Result (λ _ → ⊤)
    Mutation.Reply PatternAtomic (λ before after → after ≡ before)
    (λ _ _ → Maybe PatternInput) (λ _ _ → patternObservation) finishPattern patternSucceeded (λ _ → ⊤)

  patternProgram : PatternInput → Mutation.E.Script Mutation.Result
  patternProgram (situation , approach , success , project) = Mutation.makePattern situation approach success project

  patternInterrupted : ∀ input before after → PatternRecovery.Interrupted (patternProgram input) before after → after ≡ before
  patternInterrupted (situation , approach , success , project) before after attempt with GraphNumerics.probability success
  ... | false with attempt
  ...   | ()
  patternInterrupted (situation , approach , success , project) before after attempt | true with attempt
  ... | PatternRecovery.stopped same = same
  ... | PatternRecovery.replied {reply = inj₁ error} atomic ()
  ... | PatternRecovery.replied {reply = inj₂ value} atomic ()

  patternFailed : ∀ input before after → PatternRecovery.Failed (patternProgram input) before after → after ≡ before
  patternFailed (situation , approach , success , project) before after attempt with GraphNumerics.probability success
  ... | false with attempt
  ...   | PatternRecovery.failedReturn notSuccessful = refl
  patternFailed (situation , approach , success , project) before after attempt | true with attempt
  ... | PatternRecovery.failedReply {reply = inj₁ error} same (PatternRecovery.failedReturn notSuccessful) = same
  ... | PatternRecovery.failedReply {reply = inj₂ value} atomic (PatternRecovery.failedReturn notSuccessful) = ⊥-elim (notSuccessful tt)

  patternAchieves : ∀ input before after → PatternRecovery.Completed (patternProgram input) before after →
    patternObservation after ≡ just input
  patternAchieves (situation , approach , success , project) before after complete with GraphNumerics.probability success
  ... | false with complete
  ...   | PatternRecovery.returned ()
  patternAchieves (situation , approach , success , project) before after complete | true with complete
  ... | PatternRecovery.replied {reply = inj₁ error} atomic (PatternRecovery.returned ())
  ... | PatternRecovery.replied {reply = inj₂ value} {middle = (store , previous)}
    (unchanged , publication) (PatternRecovery.returned succeeded)
    rewrite PatternPublished.patternStored publication | PatternPublished.situationMatches publication |
      PatternPublished.approachMatches publication | PatternPublished.successMatches publication |
      PatternPublished.projectMatches publication = refl

  atomicPattern : PatternRecovery.AllOrNothing PatternInput
  atomicPattern = record
    { expected = λ input _ _ → just input
    ; script = patternProgram
    ; interruptedUnchanged = patternInterrupted
    ; failedUnchanged = patternFailed
    ; achieves = λ input before after complete _ → patternAchieves input before after complete
    }
  module PatternProof = PatternRecovery.Transactional atomicPattern
  patternOperation : PatternRecovery.Recoverable PatternInput
  patternOperation = PatternProof.transactional

  BeliefFields = Text × Float × Float × Maybe Text × Candidates.Memory
  BeliefWorld = Store.World × Maybe Graph.BeliefValues

  beliefFields : Graph.BeliefValues → BeliefFields
  beliefFields belief = Graph.BeliefValues.content belief , Graph.BeliefValues.probability belief ,
    Graph.BeliefValues.confidence belief , Graph.BeliefValues.project belief , Graph.BeliefValues.memory belief

  draftFields : BeliefEmbedding.Draft → BeliefFields
  draftFields proposal = BeliefEmbedding.Draft.content proposal , BeliefEmbedding.Draft.probability proposal ,
    BeliefEmbedding.Draft.confidence proposal , BeliefEmbedding.Draft.project proposal , BeliefEmbedding.Draft.memory proposal

  beliefView : Maybe Graph.BeliefValues → Maybe BeliefFields
  beliefView nothing = nothing
  beliefView (just belief) = just (beliefFields belief)

  beliefObservation : BeliefWorld → Maybe BeliefFields
  beliefObservation (store , nothing) = nothing
  beliefObservation (store , just returned) = beliefView
    (Ranking.lookup (Graph.BeliefValues.identity returned) (Store.beliefs store))

  finishBelief : BeliefEmbedding.Result → BeliefWorld → BeliefWorld
  finishBelief (inj₂ belief) (store , previous) = store , just belief
  finishBelief (inj₁ failure) world = world

  beliefSucceeded : BeliefEmbedding.Result → Set
  beliefSucceeded (inj₂ belief) = ⊤
  beliefSucceeded (inj₁ failure) = ⊥

  BeliefAtomic : BeliefWorld → (effect : BeliefEmbedding.Effect) → BeliefEmbedding.Reply effect → BeliefWorld → Set
  BeliefAtomic (before , previous) (BeliefEmbedding.publish proposal material) (inj₂ belief) (after , last) =
    (last ≡ previous) × BeliefPublished proposal material belief before after
  BeliefAtomic before _ _ after = after ≡ before

  module BeliefRecovery = Recovery BeliefWorld BeliefEmbedding.Effect BeliefEmbedding.Result (λ _ → ⊤)
    BeliefEmbedding.Reply BeliefAtomic (λ before after → after ≡ before)
    (λ _ _ → Maybe BeliefFields) (λ _ _ → beliefObservation) finishBelief beliefSucceeded (λ _ → ⊤)

  BeliefInput = BeliefEmbedding.Draft × BeliefEmbedding.Prepared

  publicationResult : Text ⊎ Graph.BeliefValues → BeliefEmbedding.Result
  publicationResult (inj₁ error) = inj₁ (BeliefEmbedding.publicationFailed error)
  publicationResult (inj₂ belief) = inj₂ belief

  beliefPublicationSuccess : ∀ proposal material before reply after →
    BeliefAtomic before (BeliefEmbedding.publish proposal material) reply after →
    beliefSucceeded (publicationResult reply) →
    beliefObservation (finishBelief (publicationResult reply) after) ≡ just (draftFields proposal)
  beliefPublicationSuccess proposal material before (inj₁ error) after atomic ()
  beliefPublicationSuccess proposal material before (inj₂ belief) (store , last) (unchanged , publication) succeeded
    rewrite BeliefPublished.beliefStored publication | BeliefPublished.contentMatches publication |
      BeliefPublished.probabilityMatches publication | BeliefPublished.confidenceMatches publication |
      BeliefPublished.projectMatches publication | BeliefPublished.memoryMatches publication = refl

  beliefCall : BeliefRecovery.FinalCall BeliefInput
  beliefCall = record
    { effect = λ { (proposal , material) → BeliefEmbedding.publish proposal material }
    ; answer = λ { (proposal , material) → publicationResult }
    ; expected = λ { (proposal , material) _ _ → just (draftFields proposal) }
    ; success = λ { (proposal , material) before reply after atomic succeeded _ →
        beliefPublicationSuccess proposal material before reply after atomic succeeded }
    ; failureUnchanged = λ { (proposal , material) before (inj₁ error) after same notSuccessful → same
                          ; (proposal , material) before (inj₂ belief) after atomic notSuccessful → ⊥-elim (notSuccessful tt) }
    ; crashUnchanged = λ _ _ same → same
    }
  module BeliefProof = BeliefRecovery.FinalPublication beliefCall
  beliefOperation : BeliefRecovery.Recoverable BeliefInput
  beliefOperation = BeliefProof.finalPublication

  record SearchRequest : Set where
    constructor searchRequest
    field
      query : Text
      limit : Maybe ℕ
      project : Maybe Text
      prefer : Maybe Candidates.Memory
      includeEvidence : Bool
      evidencePerBelief : Maybe ℕ

  data SearchPhase : Set where
    retrieving : Bool → Maybe ℕ → Retrieval.State → SearchPhase
    collectingEvidence : Evidence.E.Script (Text ⊎ List Evidence.Grounded) → SearchPhase

  data SearchEffect : Set where
    retrieval : Retrieval.State → SearchEffect
    evidence : Evidence.Effect → SearchEffect

  SearchReply : SearchEffect → Set
  SearchReply (retrieval state) = Retrieval.Reply state
  SearchReply (evidence effect) = Evidence.Reply effect

  searchSucceeded : Result → Set
  searchSucceeded (relevantResult _) = ⊤
  searchSucceeded (groundedResult (inj₂ _)) = ⊤
  searchSucceeded _ = ⊥

  module SearchRecovery = Recovery Store.World SearchEffect Result (λ _ → ⊤) SearchReply
    (λ before effect reply after → after ≡ before) (λ before after → after ≡ before)
    (λ _ _ → Store.World) (λ _ _ world → world) (λ _ world → world) searchSucceeded (λ _ → ⊤)

  evidenceSearchNext : Evidence.E.Script (Text ⊎ List Evidence.Grounded) → SearchRecovery.Next SearchPhase
  evidenceSearchNext (Evidence.E.done result) = SearchRecovery.Next.returned (groundedResult result)
  evidenceSearchNext (Evidence.E.ask effect continuation) = SearchRecovery.Next.perform (evidence effect)
    (λ reply → collectingEvidence (continuation reply))

  searchNext : SearchPhase → SearchRecovery.Next SearchPhase
  searchNext (collectingEvidence program) = evidenceSearchNext program
  searchNext (retrieving false per (Retrieval.finished result)) = SearchRecovery.Next.returned (relevantResult result)
  searchNext (retrieving true per (Retrieval.finished result)) = evidenceSearchNext (Evidence.many per result)
  searchNext (retrieving include per (Retrieval.failed error)) = SearchRecovery.Next.returned (failed error)
  searchNext (retrieving include per state@(Retrieval.overlay _)) = SearchRecovery.Next.perform (retrieval state)
    (λ reply → retrieving include per (Retrieve.advance state reply))
  searchNext (retrieving include per state@(Retrieval.beliefs _ _)) = SearchRecovery.Next.perform (retrieval state)
    (λ reply → retrieving include per (Retrieve.advance state reply))
  searchNext (retrieving include per state@(Retrieval.embedding _ _ _ _)) = SearchRecovery.Next.perform (retrieval state)
    (λ reply → retrieving include per (Retrieve.advance state reply))
  searchNext (retrieving include per state@(Retrieval.vectorQuery _ _ _ _ _)) = SearchRecovery.Next.perform (retrieval state)
    (λ reply → retrieving include per (Retrieve.advance state reply))
  searchNext (retrieving include per state@(Retrieval.closure _ _ _)) = SearchRecovery.Next.perform (retrieval state)
    (λ reply → retrieving include per (Retrieve.advance state reply))
  searchNext (retrieving include per state@(Retrieval.neighbors _ _ _ _ _ _)) = SearchRecovery.Next.perform (retrieval state)
    (λ reply → retrieving include per (Retrieve.advance state reply))

  searchMachine : SearchRecovery.Machine
  searchMachine = record { State = SearchPhase ; next = searchNext }
  module SearchProof = SearchRecovery.ReadOnlyMachine searchMachine (λ _ _ _ _ same → same)
    (λ _ _ same → same) (λ _ _ → refl)

  preference : Bool → Maybe Candidates.Memory → Maybe Candidates.Memory
  preference false requested = requested
  preference true requested = nothing

  searchOperation : SearchRecovery.Recoverable SearchRequest
  searchOperation = SearchProof.readOnly (λ request → retrieving
    (SearchRequest.includeEvidence request) (SearchRequest.evidencePerBelief request)
    (Retrieval.overlay (Retrieval.request (SearchRequest.query request) (SearchRequest.limit request)
      (SearchRequest.project request) (preference (SearchRequest.includeEvidence request) (SearchRequest.prefer request)) embeddingsEnabled)))

  contextSucceeded : Result → Set
  contextSucceeded (contextResult _) = ⊤
  contextSucceeded _ = ⊥
  module ContextRecovery = Recovery Store.World Context.State Result (λ _ → ⊤) Context.Reply
    (λ before effect reply after → after ≡ before) (λ before after → after ≡ before)
    (λ _ _ → Store.World) (λ _ _ world → world) (λ _ world → world) contextSucceeded (λ _ → ⊤)

  contextNext : Context.State → ContextRecovery.Next Context.State
  contextNext (Context.finished result) = ContextRecovery.Next.returned (contextResult result)
  contextNext (Context.failed error) = ContextRecovery.Next.returned (failed error)
  contextNext Context.invalidInput = ContextRecovery.Next.returned invalidContext
  contextNext Context.invalidAssessment = ContextRecovery.Next.returned invalidAssessment
  contextNext state@(Context.retrieving _ _) = ContextRecovery.Next.perform state (LearningContext.advance state)
  contextNext state@(Context.patternResults _ _) = ContextRecovery.Next.perform state (LearningContext.advance state)
  contextNext state@(Context.assessmentGroups _ _ _) = ContextRecovery.Next.perform state (LearningContext.advance state)

  contextMachine : ContextRecovery.Machine
  contextMachine = record { State = Context.State ; next = contextNext }
  module ContextProof = ContextRecovery.ReadOnlyMachine contextMachine (λ _ _ _ _ same → same)
    (λ _ _ same → same) (λ _ _ → refl)
  ContextInput = Text × Text × Maybe ℕ
  contextOperation : ContextRecovery.Recoverable ContextInput
  contextOperation = ContextProof.readOnly (λ { (query , project , limit) →
    LearningContext.begin (Context.contextRequest query project limit embeddingsEnabled) })

  OrdinaryRelation : Mutation.Statement → Set
  OrdinaryRelation (Mutation.insertEdge from to Relations.defeats weight) = ⊥
  OrdinaryRelation _ = ⊤

  data AdmissionFault : Set where
    groundingInput relationWeight requestIdentity invalidBeliefOrigin retirementPolicy : AdmissionFault
    beliefDecision : BeliefEmbedding.Failure → AdmissionFault
    documentProblem : Text → AdmissionFault
    documentShape documentBackend : AdmissionFault

  admissionResult : AdmissionFault → Result
  admissionResult groundingInput = invalidGrounding
  admissionResult relationWeight = mutated Mutation.invalidEdgeWeight
  admissionResult invalidBeliefOrigin = mutated Mutation.invalidOrigin
  admissionResult (beliefDecision failure) = mutated (Mutation.embeddingFailed failure)
  admissionResult requestIdentity = invalidRequestIdentity
  admissionResult retirementPolicy = needsDecision
    (Envelope.literal "Sweeping is paused: [retirement].grace_hours is unset. No deletion was attempted.")
    (Envelope.literal "Ask the user to choose a retention period in configuration, then retry. Do not choose it for the user or pass a per-call override.")
  admissionResult (documentProblem detail) = documentResult (Document.failed detail)
  admissionResult documentShape = documentResult Document.invalidEmbeddingShape
  admissionResult documentBackend = documentResult Document.embeddingsDisabled

  data PreparationRequest : Set where
    prepareBeliefInput : (proposal : BeliefEmbedding.Draft) →
      BeliefEmbedding.admit embeddingsEnabled proposal ≡ nothing → PreparationRequest
    canonicalLoadInput readDocumentInput : Text → Maybe Text → PreparationRequest
    embedDocumentInput : Text → List DocumentStore.Chunk → PreparationRequest
    canonicalClearInput : Text → PreparationRequest

  PreparationReply : PreparationRequest → Set
  PreparationReply (prepareBeliefInput proposal admitted) = BeliefEmbedding.Preparation
  PreparationReply (canonicalLoadInput path project) = Text ⊎ Text
  PreparationReply (readDocumentInput path project) = Text ⊎ Text
  PreparationReply (embedDocumentInput path chunks) = Text ⊎ List Store.Vector
  PreparationReply (canonicalClearInput path) = Text ⊎ Text

  PreparationResult = Σ PreparationRequest PreparationReply

  module PreparationRecovery = Recovery Store.World PreparationRequest PreparationResult
    (λ _ → ⊤) PreparationReply (λ before _ _ after → after ≡ before)
    (λ before after → after ≡ before) (λ _ _ → Store.World)
    (λ _ _ world → world) (λ _ world → world) (λ _ → ⊤) (λ _ → ⊤)
  module PreparationProof = PreparationRecovery.ReadOnly
    (λ _ _ _ _ same → same) (λ _ _ same → same) (λ _ _ → refl)

  preparationProgram : PreparationRequest → PreparationRecovery.E.Script PreparationResult
  preparationProgram request = PreparationRecovery.E.ask request
    (λ reply → PreparationRecovery.E.done (request , reply))

  preparationOperation : PreparationRecovery.Recoverable PreparationRequest
  preparationOperation = PreparationProof.readOnly preparationProgram

  data State : Set where
    correcting : AdmissionFault → State
    capabilityState : Capability.RunState capabilityOperation tt → State
    requestState : Envelope.Identity → State → State
    defeatState : (from to : UUID) → (weight : Number) →
      DefeatRecovery.Proof.RunState from to weight (DefeatRecovery.recovery from to weight) tt → State
    patternState : (input : PatternInput) → PatternRecovery.RunState patternOperation input → State
    preparationState : (request : PreparationRequest) →
      PreparationRecovery.RunState preparationOperation request → State
    publishingBelief : (input : BeliefInput) → BeliefRecovery.RunState beliefOperation input → State
    relationState : (command : Mutation.Statement) → OrdinaryRelation command →
      RelationRecovery.Proof.RunState command (RelationRecovery.recovery command) tt → State
    readState : (request : Read.Request) → ReadRecovery.RunState readOperation request → State
    deleteState : (kind : Deletion.Kind) → (id : UUID) →
      DeleteRecovery.R.RunState kind id (DeleteRecovery.recovery kind id) tt → State
    standaloneForgetState : (project : Text) →
      Standalone.R.RunState project (Standalone.recovery project) tt → State
    preparingInference : (request : Inference.Request) →
      InferencePreparationRecovery.RunState inferencePreparationOperation request → State
    publishingPosteriors : (writes : Posterior.State) → (result : Inference.Result) →
      (successful : Inference.Successful result) →
      PosteriorRecovery.R.RunState writes result successful (PosteriorRecovery.recovery writes result successful) tt → State
    sweeping : (ids : List UUID) →
      Sweep.Certified.R.RunState ids (Sweep.Certified.recovery ids) tt → State
    inferenceQueryState : (request : Inference.ReadRequest) →
      InferenceQueryRecovery.RunState inferenceQueryOperation request → State
    groundState : (request : Ground.Request) →
      GroundRecovery.R.RunState request (GroundRecovery.recovery request) tt → State
    evidenceState : (request : EvidenceRequest) → EvidenceRecovery.RunState evidenceOperation request → State
    publishingDocument : (path : Text) → (chunks : List DocumentStore.Chunk) → (vectors : List Store.Vector) →
      DocumentReplaceRecovery.R.RunState path chunks vectors
        (DocumentReplaceRecovery.recovery path chunks vectors) tt → State
    clearingDocument : (path : Text) →
      DocumentClearRecovery.R.RunState path (DocumentClearRecovery.recovery path) tt → State
    documentQueryState : (request : DocumentSearch) → DocumentSearchRecovery.RunState documentSearchOperation request → State
    preparingLearning : (q : Learning.Request) →
      LearningRecovery.P.RunState q (LearningRecovery.preparation q) tt → State
    publishingLearning : (q : Learning.Request) → (tx : Learn.T.Transaction q) →
      (proposed : LearningStore.World) → (value : Observation.Snapshot) →
      LearningRecovery.Commit.R.RunState q tx proposed value
        (LearningRecovery.Commit.recovery q tx proposed value) tt → State
    queryState : (request : Query.Request) → QueryRecovery.RunState queryOperation request → State
    searchState : (request : SearchRequest) → SearchRecovery.RunState searchOperation request → State
    contextState : (input : ContextInput) → ContextRecovery.RunState contextOperation input → State

  beginPreparation : PreparationRequest → State
  beginPreparation request = preparationState request (PreparationRecovery.start preparationOperation request)

  preparingBelief : (proposal : BeliefEmbedding.Draft) →
    BeliefEmbedding.admit embeddingsEnabled proposal ≡ nothing → State
  preparingBelief proposal admitted = beginPreparation (prepareBeliefInput proposal admitted)

  canonicalizingDocumentLoad : Text → Maybe Text → State
  canonicalizingDocumentLoad path project = beginPreparation (canonicalLoadInput path project)

  canonicalizingDocumentClear : Text → State
  canonicalizingDocumentClear path = beginPreparation (canonicalClearInput path)

  data Effect : Set where
    mutationEffect : Mutation.Effect → Effect
    readEffect : Read.Effect → Effect
    deleteEffect : Delete.T.Effect → Effect
    forgetEffect : Forget.Effect → Effect
    inferenceEffect : Inference.Effect → Effect
    inferenceQueryEffect : Inference.ReadEffect → Effect
    inferencePreparationEffect : Inference.ReadEffect → Effect
    sweepEffect : Sweep.S.Effect → Effect
    groundEffect : Grounding.T.Effect → Effect
    evidenceEffect : Evidence.Effect → Effect
    documentEffect : Document.Effect → Effect
    documentClearEffect : Document.T.Effect → Effect
    documentPublicationEffect : Document.T.Effect → Effect
    documentQueryEffect : DocumentQuery.Effect → Effect
    learningPreparationEffect : (q : Learning.Request) → Learn.PreparationEffect q → Effect
    learningCommitEffect : (q : Learning.Request) → Learn.T.Transaction q →
      LearningStore.World → Observation.Snapshot → Effect
    queryEffect : Query.Effect → Effect
    searchEffect : SearchEffect → Effect
    contextEffect : Context.State → Effect

  Reply : Effect → Set
  Reply (mutationEffect e) = Mutation.Reply e
  Reply (readEffect e) = Read.Reply e
  Reply (deleteEffect e) = Delete.T.Reply e
  Reply (forgetEffect e) = Forget.Reply e
  Reply (inferenceEffect e) = Inference.Reply e
  Reply (inferenceQueryEffect e) = Inference.ReadReply e
  Reply (inferencePreparationEffect e) = Inference.ReadReply e
  Reply (sweepEffect e) = Sweep.S.Reply e
  Reply (groundEffect e) = Grounding.T.Reply e
  Reply (evidenceEffect e) = Evidence.Reply e
  Reply (documentEffect e) = Document.Reply e
  Reply (documentClearEffect e) = Document.T.Reply e
  Reply (documentPublicationEffect e) = Document.T.Reply e
  Reply (documentQueryEffect e) = DocumentQuery.Reply e
  Reply (learningPreparationEffect q e) = Learn.PreparationReply q e
  Reply (learningCommitEffect q tx proposed value) = Learn.T.CommitReply q
  Reply (queryEffect e) = Query.Reply e
  Reply (searchEffect effect) = SearchReply effect
  Reply (contextEffect s) = Context.Reply s

  data Next : Set where
    complete : Result → Next
    perform : (effect : Effect) → (Reply effect → State) → Next

  learningCommitNext : ∀ q tx proposed value →
    LearningRecovery.Commit.R.RunState q tx proposed value
      (LearningRecovery.Commit.recovery q tx proposed value) tt → Next
  learningCommitNext q tx proposed value (LearningRecovery.Commit.R.running events
    (LearningRecovery.Commit.R.E.done answer) prefix) = complete (learned q answer)
  learningCommitNext q tx proposed value (LearningRecovery.Commit.R.running events
    (LearningRecovery.Commit.R.E.ask tt continuation) prefix) =
    perform (learningCommitEffect q tx proposed value) (λ reply → publishingLearning q tx proposed value
      (LearningRecovery.Commit.R.advance q tx proposed value
        (LearningRecovery.Commit.recovery q tx proposed value) tt events tt continuation prefix refl reply))

  learningPreparationNext : ∀ q →
    LearningRecovery.P.RunState q (LearningRecovery.preparation q) tt → Next
  learningPreparationNext q (LearningRecovery.P.running events
    (LearningRecovery.P.E.done (Learn.invalidPreparation failure)) prefix) =
    complete (learned q (Learn.invalidRequest failure))
  learningPreparationNext q (LearningRecovery.P.running events
    (LearningRecovery.P.E.done (Learn.transactionPrepared (Learn.Stage.complete outcome proof))) prefix) =
    complete (learned q (Learn.transacted outcome))
  learningPreparationNext q (LearningRecovery.P.running events
    (LearningRecovery.P.E.done (Learn.transactionPrepared (Learn.Stage.ready tx proposed value))) prefix) =
    learningCommitNext q tx proposed value
      (LearningRecovery.Commit.R.start q tx proposed value (LearningRecovery.Commit.recovery q tx proposed value) tt)
  learningPreparationNext q (LearningRecovery.P.running events
    (LearningRecovery.P.E.ask effect continuation) prefix) =
    perform (learningPreparationEffect q effect) (λ reply → preparingLearning q
      (LearningRecovery.P.advance q (LearningRecovery.preparation q) tt
        events effect continuation prefix refl reply))

  posteriorNext : ∀ writes result successful →
    PosteriorRecovery.R.RunState writes result successful (PosteriorRecovery.recovery writes result successful) tt → Next
  posteriorNext writes result successful (PosteriorRecovery.R.running events
    (PosteriorRecovery.R.E.done answer) prefix) = complete (inferred answer)
  posteriorNext writes result successful (PosteriorRecovery.R.running events
    (PosteriorRecovery.R.E.ask tt continuation) prefix) =
    perform (inferenceEffect (Inference.persistBeta writes)) (λ reply → publishingPosteriors writes result successful
      (PosteriorRecovery.R.advance writes result successful (PosteriorRecovery.recovery writes result successful) tt
        events tt continuation prefix refl reply))

  sweepNext : ∀ ids → Sweep.Certified.R.RunState ids (Sweep.Certified.recovery ids) tt → Next
  sweepNext ids (Sweep.Certified.R.running events (Sweep.S.E.done result) prefix) = complete (swept result)
  sweepNext ids (Sweep.Certified.R.running events (Sweep.S.E.ask effect continuation) prefix) =
    perform (sweepEffect effect) (λ reply → sweeping ids
      (Sweep.Certified.R.advance ids (Sweep.Certified.recovery ids) tt events effect continuation prefix refl reply))

  evidenceNext : (request : EvidenceRequest) → EvidenceRecovery.RunState evidenceOperation request → Next
  evidenceNext request (EvidenceRecovery.running events (EvidenceRecovery.E.done result) prefix) = complete result
  evidenceNext request (EvidenceRecovery.running events (EvidenceRecovery.E.ask effect continuation) prefix) =
    perform (evidenceEffect effect) (λ reply → evidenceState request
      (EvidenceRecovery.advance evidenceOperation request events effect continuation prefix refl reply))

  beliefPublicationNext : (input : BeliefInput) → BeliefRecovery.RunState beliefOperation input → Next
  beliefPublicationNext input (BeliefRecovery.running events (BeliefRecovery.E.done (inj₁ failure)) prefix) =
    complete (mutated (Mutation.embeddingFailed failure))
  beliefPublicationNext input (BeliefRecovery.running events (BeliefRecovery.E.done (inj₂ belief)) prefix) =
    complete (mutated (Mutation.insertedBelief belief))
  beliefPublicationNext input (BeliefRecovery.running events (BeliefRecovery.E.ask effect continuation) prefix) =
    perform (mutationEffect (Mutation.embedding effect)) (λ reply → publishingBelief input
      (BeliefRecovery.advance beliefOperation input events effect continuation prefix refl reply))

  documentPublicationNext : ∀ path chunks vectors →
    DocumentReplaceRecovery.R.RunState path chunks vectors
      (DocumentReplaceRecovery.recovery path chunks vectors) tt → Next
  documentPublicationNext path chunks vectors (DocumentReplaceRecovery.R.running events
    (Document.T.E.done result) prefix) = complete (documentResult (Document.replaceOutcome result))
  documentPublicationNext path chunks vectors (DocumentReplaceRecovery.R.running events
    (Document.T.E.ask effect continuation) prefix) =
    perform (documentPublicationEffect effect) (λ reply → publishingDocument path chunks vectors
      (DocumentReplaceRecovery.R.advance path chunks vectors (DocumentReplaceRecovery.recovery path chunks vectors) tt
        events effect continuation prefix refl reply))

  documentClearNext : ∀ path →
    DocumentClearRecovery.R.RunState path (DocumentClearRecovery.recovery path) tt → Next
  documentClearNext path (DocumentClearRecovery.R.running events (Document.T.E.done result) prefix) =
    complete (documentResult (Document.clearOutcome result))
  documentClearNext path (DocumentClearRecovery.R.running events (Document.T.E.ask effect continuation) prefix) =
    perform (documentClearEffect effect) (λ reply → clearingDocument path
      (DocumentClearRecovery.R.advance path (DocumentClearRecovery.recovery path) tt
        events effect continuation prefix refl reply))

  preparationExternal : (request : PreparationRequest) → (PreparationReply request → State) → Next
  preparationExternal (prepareBeliefInput proposal admitted) continuation =
    perform (mutationEffect (Mutation.embedding (BeliefEmbedding.prepare proposal))) continuation
  preparationExternal (canonicalLoadInput path project) continuation =
    perform (documentEffect (Document.canonicalize path)) continuation
  preparationExternal (readDocumentInput path project) continuation =
    perform (documentEffect (Document.readUTF8 path)) continuation
  preparationExternal (embedDocumentInput path chunks) continuation =
    perform (documentEffect (Document.embed (map DocumentStore.Chunk.content chunks))) continuation
  preparationExternal (canonicalClearInput path) continuation =
    perform (documentEffect (Document.canonicalize path)) continuation

  preparationFirst : PreparationRequest → Next
  preparationFirst request = preparationExternal request (λ reply → preparationState request
    (PreparationRecovery.advance preparationOperation request [] request
      (λ received → PreparationRecovery.E.done (request , received))
      (PreparationRecovery.MachineRuns.stopped _) refl reply))

  clearDocumentPath : Text → Text ⊎ Text → Text
  clearDocumentPath supplied (inj₁ detail) = supplied
  clearDocumentPath supplied (inj₂ canonical) = canonical

  preparationComplete : PreparationResult → Next
  preparationComplete (prepareBeliefInput proposal admitted , BeliefEmbedding.askUser reason guidance) =
    complete (admissionResult (beliefDecision (BeliefEmbedding.needsInput reason guidance)))
  preparationComplete (prepareBeliefInput proposal admitted , BeliefEmbedding.ready material) =
    beliefPublicationNext (proposal , material) (BeliefRecovery.start beliefOperation (proposal , material))
  preparationComplete (canonicalLoadInput path project , inj₁ detail) = complete (admissionResult (documentProblem detail))
  preparationComplete (canonicalLoadInput path project , inj₂ canonical) = preparationFirst (readDocumentInput canonical project)
  preparationComplete (readDocumentInput path project , inj₁ detail) = complete (admissionResult (documentProblem detail))
  preparationComplete (readDocumentInput path project , inj₂ text) =
    preparationFirst (embedDocumentInput path (Document.chunksFrom chunkIdentity path project text))
  preparationComplete (embedDocumentInput path chunks , inj₁ detail) = complete (admissionResult (documentProblem detail))
  preparationComplete (embedDocumentInput path chunks , inj₂ vectors) with Document.P.align chunks vectors
  ... | nothing = complete (admissionResult documentShape)
  ... | just aligned = documentPublicationNext path chunks vectors
    (DocumentReplaceRecovery.R.start path chunks vectors (DocumentReplaceRecovery.recovery path chunks vectors) tt)
  preparationComplete (canonicalClearInput path , resolution) = documentClearNext selected
    (DocumentClearRecovery.R.start selected (DocumentClearRecovery.recovery selected) tt)
    where selected = clearDocumentPath path resolution

  next : State → Next
  next (correcting fault) = complete (admissionResult fault)
  next (capabilityState (Capability.running events (Capability.E.done result) prefix)) = complete result
  next (capabilityState (Capability.running events (Capability.E.ask () continuation) prefix))
  next (requestState identityValue state) with next state
  ... | complete result = complete result
  ... | perform effect continuation = perform effect (λ reply → requestState identityValue (continuation reply))
  next (defeatState from to weight (DefeatRecovery.Proof.running events
    (DefeatRecovery.Proof.E.done result) prefix)) = complete (mutated result)
  next (defeatState from to weight (DefeatRecovery.Proof.running events
    (DefeatRecovery.Proof.E.ask tt continuation) prefix)) =
    perform (mutationEffect (Mutation.recordDefeat from to weight)) (λ reply → defeatState from to weight
      (DefeatRecovery.Proof.advance from to weight (DefeatRecovery.recovery from to weight) tt
        events tt continuation prefix refl reply))
  next (patternState input (PatternRecovery.running events (PatternRecovery.E.done result) prefix)) = complete (mutated result)
  next (patternState input (PatternRecovery.running events (PatternRecovery.E.ask effect continuation) prefix)) =
    perform (mutationEffect effect) (λ reply → patternState input
      (PatternRecovery.advance patternOperation input events effect continuation prefix refl reply))
  next (preparationState request (PreparationRecovery.running events (PreparationRecovery.E.done result) prefix)) =
    preparationComplete result
  next (preparationState request (PreparationRecovery.running events (PreparationRecovery.E.ask effect continuation) prefix)) =
    preparationExternal effect (λ reply → preparationState request
      (PreparationRecovery.advance preparationOperation request events effect continuation prefix refl reply))
  next (publishingBelief input state) = beliefPublicationNext input state
  next (relationState command admitted (RelationRecovery.Proof.running events (RelationRecovery.Proof.E.done result) prefix)) =
    complete (mutated result)
  next (relationState command admitted (RelationRecovery.Proof.running events (RelationRecovery.Proof.E.ask effect continuation) prefix)) =
    perform (mutationEffect effect) (λ reply → relationState command admitted
      (RelationRecovery.Proof.advance command (RelationRecovery.recovery command) tt events effect continuation prefix refl reply))
  next (readState request (ReadRecovery.running events (ReadRecovery.E.done result) prefix)) = complete (readResult result)
  next (readState request (ReadRecovery.running events (ReadRecovery.E.ask effect continuation) prefix)) =
    perform (readEffect effect) (λ reply → readState request
      (ReadRecovery.advance readOperation request events effect continuation prefix refl reply))
  next (deleteState kind id (DeleteRecovery.R.running events (DeleteRecovery.R.E.done result) prefix)) = complete (deleted result)
  next (deleteState kind id (DeleteRecovery.R.running events (DeleteRecovery.R.E.ask effect continuation) prefix)) =
    perform (deleteEffect effect) (λ reply → deleteState kind id
      (DeleteRecovery.R.advance kind id (DeleteRecovery.recovery kind id) tt events effect continuation prefix refl reply))
  next (standaloneForgetState project (Standalone.R.running events (Standalone.R.E.done result) prefix)) =
    complete (forgotten result)
  next (standaloneForgetState project (Standalone.R.running events (Standalone.R.E.ask effect continuation) prefix)) =
    perform (forgetEffect effect) (λ reply → standaloneForgetState project
      (Standalone.R.advance project (Standalone.recovery project) tt events effect continuation prefix refl reply))
  next (preparingInference request (InferencePreparationRecovery.running events
    (InferencePreparationRecovery.E.done (Inference.noPublication result)) prefix)) = complete (inferred result)
  next (preparingInference request (InferencePreparationRecovery.running events
    (InferencePreparationRecovery.E.done (Inference.publish (Inference.update writes result successful))) prefix)) =
    posteriorNext writes result successful
      (PosteriorRecovery.R.start writes result successful (PosteriorRecovery.recovery writes result successful) tt)
  next (preparingInference request (InferencePreparationRecovery.running events
    (InferencePreparationRecovery.E.done (Inference.publish (Inference.removeSelection ids))) prefix)) =
    sweepNext ids (Sweep.Certified.R.start ids (Sweep.Certified.recovery ids) tt)
  next (preparingInference request (InferencePreparationRecovery.running events
    (InferencePreparationRecovery.E.ask effect continuation) prefix)) =
    perform (inferencePreparationEffect effect) (λ reply → preparingInference request
      (InferencePreparationRecovery.advance inferencePreparationOperation request events effect continuation prefix refl reply))
  next (publishingPosteriors writes result successful state) = posteriorNext writes result successful state
  next (sweeping ids state) = sweepNext ids state
  next (inferenceQueryState request (InferenceQueryRecovery.running events
    (InferenceQueryRecovery.E.done result) prefix)) = complete (inferred result)
  next (inferenceQueryState request (InferenceQueryRecovery.running events
    (InferenceQueryRecovery.E.ask effect continuation) prefix)) =
    perform (inferenceQueryEffect effect) (λ reply → inferenceQueryState request
      (InferenceQueryRecovery.advance inferenceQueryOperation request events effect continuation prefix refl reply))
  next (groundState request (GroundRecovery.R.running events (GroundRecovery.R.E.done result) prefix)) = complete (grounded result)
  next (groundState request (GroundRecovery.R.running events (GroundRecovery.R.E.ask effect continuation) prefix)) =
    perform (groundEffect effect) (λ reply → groundState request
      (GroundRecovery.R.advance request (GroundRecovery.recovery request) tt events effect continuation prefix refl reply))
  next (evidenceState request state) = evidenceNext request state
  next (publishingDocument path chunks vectors state) = documentPublicationNext path chunks vectors state
  next (clearingDocument path state) = documentClearNext path state
  next (documentQueryState request (DocumentSearchRecovery.running events (DocumentSearchRecovery.E.done result) prefix)) =
    complete (documentQueryResult result)
  next (documentQueryState request (DocumentSearchRecovery.running events (DocumentSearchRecovery.E.ask effect continuation) prefix)) =
    perform (documentQueryEffect effect) (λ reply → documentQueryState request
      (DocumentSearchRecovery.advance documentSearchOperation request events effect continuation prefix refl reply))
  next (preparingLearning q state) = learningPreparationNext q state
  next (publishingLearning q tx proposed value state) = learningCommitNext q tx proposed value state
  next (queryState request (QueryRecovery.running events (QueryRecovery.E.done result) prefix)) = complete (learningQueryResult result)
  next (queryState request (QueryRecovery.running events (QueryRecovery.E.ask effect continuation) prefix)) =
    perform (queryEffect effect) (λ reply → queryState request
      (QueryRecovery.advance queryOperation request events effect continuation prefix refl reply))
  next (searchState request (SearchRecovery.running events phase prefix)) with searchNext phase in ready
  ... | SearchRecovery.Next.returned result = complete result
  ... | SearchRecovery.Next.perform effect continuation = perform (searchEffect effect) (λ reply →
    searchState request (SearchRecovery.advance searchOperation request events effect continuation prefix ready reply))
  next (contextState input (ContextRecovery.running events phase prefix)) with contextNext phase in ready
  ... | ContextRecovery.Next.returned result = complete result
  ... | ContextRecovery.Next.perform effect continuation = perform (contextEffect effect) (λ reply →
    contextState input (ContextRecovery.advance contextOperation input events effect continuation prefix ready reply))

  groundStart : UUID → UUID → Float → State
  groundStart belief chunk weight with Ground.admitted (Ground.add chunk belief weight)
  ... | false = correcting groundingInput
  ... | true = groundState (Ground.add chunk belief weight)
    (GroundRecovery.R.start (Ground.add chunk belief weight) (GroundRecovery.recovery (Ground.add chunk belief weight)) tt)

  ordinaryRelationStart : (command : Mutation.Statement) → OrdinaryRelation command → State
  ordinaryRelationStart command admitted = relationState command admitted
    (RelationRecovery.Proof.start command (RelationRecovery.recovery command) tt)

  relationStart : UUID → UUID → Relations.Relation → Number → State
  relationStart from to relation weight with Numeric.number weight
  ... | nothing = correcting relationWeight
  ... | just value with GraphNumerics.probability value
  ...   | false = correcting relationWeight
  ...   | true with relation
  ...     | Relations.defeats = defeatState from to weight
    (DefeatRecovery.Proof.start from to weight (DefeatRecovery.recovery from to weight) tt)
  ...     | Relations.supports = ordinaryRelationStart (Mutation.insertEdge from to Relations.supports weight) tt
  ...     | Relations.causes = ordinaryRelationStart (Mutation.insertEdge from to Relations.causes weight) tt
  ...     | Relations.contradicts = ordinaryRelationStart (Mutation.insertEdge from to Relations.contradicts weight) tt

  admittedBeliefStart : BeliefEmbedding.Draft → State
  admittedBeliefStart proposal with BeliefEmbedding.admit embeddingsEnabled proposal in admitted
  ... | just failure = correcting (beliefDecision failure)
  ... | nothing = preparingBelief proposal admitted

  beliefStart : BeliefEmbedding.Draft → State
  beliefStart proposal with BeliefEmbedding.Draft.origin proposal
  ... | nothing = admittedBeliefStart proposal
  ... | just sourceMetadata with Origin.validate sourceMetadata
  ...   | Validation.rejected fault invalid = correcting invalidBeliefOrigin
  ...   | Validation.accepted valid = admittedBeliefStart proposal

  start : Public.Request → State
  start (Public.mutation (Mutation.belief content probability confidence project memory origin)) =
    beliefStart (BeliefEmbedding.draft content probability confidence project memory origin)
  start (Public.mutation (Mutation.patternNode situation approach success project)) =
    patternState (situation , approach , success , project)
      (PatternRecovery.start patternOperation (situation , approach , success , project))
  start (Public.mutation (Mutation.edge from to relation weight)) = relationStart from to relation weight
  start (Public.read request) = readState request (ReadRecovery.start readOperation request)
  start (Public.delete kind id) = deleteState kind id
    (DeleteRecovery.R.start kind id (DeleteRecovery.recovery kind id) tt)
  start (Public.deleteProject project) =
    standaloneForgetState project (Standalone.R.start project (Standalone.recovery project) tt)
  start (Public.inference request@(Inference.propagate id)) = preparingInference request
    (InferencePreparationRecovery.start inferencePreparationOperation request)
  start (Public.inference (Inference.intervention id value)) =
    inferenceQueryState (Inference.interventionView id value)
      (InferenceQueryRecovery.start inferenceQueryOperation (Inference.interventionView id value))
  start (Public.inference request@(Inference.decay project factor)) = preparingInference request
    (InferencePreparationRecovery.start inferencePreparationOperation request)
  start (Public.inference (Inference.contradictions project)) =
    inferenceQueryState (Inference.contradictionsView project)
      (InferenceQueryRecovery.start inferenceQueryOperation (Inference.contradictionsView project))
  start (Public.inference request@(Inference.sweep project threshold grace)) = preparingInference request
    (InferencePreparationRecovery.start inferencePreparationOperation request)
  start (Public.inference request@(Inference.sweepHours project threshold grace)) = preparingInference request
    (InferencePreparationRecovery.start inferencePreparationOperation request)
  start (Public.sweepConfigured project threshold) with retirementGraceHours
  ... | nothing = correcting retirementPolicy
  ... | just hours = preparingInference (Inference.sweepHours project threshold hours)
    (InferencePreparationRecovery.start inferencePreparationOperation (Inference.sweepHours project threshold hours))
  start (Public.relevant query limit project prefer include per) = searchState (searchRequest query limit project prefer include per)
    (SearchRecovery.start searchOperation (searchRequest query limit project prefer include per))
  start (Public.addEvidence belief chunk weight) = groundStart belief chunk weight
  start (Public.removeEvidence belief chunk) = groundState (Ground.remove chunk belief)
    (GroundRecovery.R.start (Ground.remove chunk belief) (GroundRecovery.recovery (Ground.remove chunk belief)) tt)
  start (Public.evidence belief) = evidenceState (oneEvidence belief)
    (EvidenceRecovery.start evidenceOperation (oneEvidence belief))
  start (Public.loadDocument path project) with embeddingsEnabled
  ... | false = correcting documentBackend
  ... | true = canonicalizingDocumentLoad path project
  start (Public.queryDocument query project limit) = documentQueryState (query , project , limit)
    (DocumentSearchRecovery.start documentSearchOperation (query , project , limit))
  start (Public.clearDocument path) = canonicalizingDocumentClear path
  start (Public.learning q) = preparingLearning q
    (LearningRecovery.P.start q (LearningRecovery.preparation q) tt)
  start (Public.learningQuery request) = queryState request (QueryRecovery.start queryOperation request)
  start (Public.learningContext query project limit) = contextState (query , project , limit)
    (ContextRecovery.start contextOperation (query , project , limit))
  start Public.capabilities = capabilityState (Capability.start capabilityOperation tt)

  startRequest : Envelope.Identity → Text → JSON.Value → Public.Request → State
  startRequest (Envelope.identity true (JSON.string id)) name arguments request =
    requestState (Envelope.identity true (JSON.string id)) (start request)
  startRequest (Envelope.identity true _) name arguments request =
    correcting requestIdentity
  startRequest (Envelope.identity false value) name arguments request =
    requestState (Envelope.identity false value) (start request)

  Event = Σ Effect Reply

  data Runs : State → List Event → Result → Set where
    returned : ∀ state result → next state ≡ complete result → Runs state [] result
    replied : ∀ state effect continuation reply events result →
      next state ≡ perform effect continuation → Runs (continuation reply) events result →
      Runs state ((effect , reply) ∷ events) result

  Ordinary : Effect → Set
  Ordinary _ = ⊥

  ForgetStaging : Forget.Effect → Set
  ForgetStaging (Forget.learning (Forget.T.read tx)) = ⊥
  ForgetStaging (Forget.learning (Forget.T.commit tx)) = ⊥
  ForgetStaging effect = ⊤

  data RequestStep : State → (effect : Effect) → Reply effect → Store.World → Store.World → Set where
    underRequest : ∀ {identity state effect reply before after} → RequestStep state effect reply before after →
      RequestStep (requestState identity state) effect reply before after
    preparedDocumentPublication : ∀ {request events path chunks vectors prefix reply before after} →
      DocumentReplaceRecovery.Atomic path chunks vectors before (Document.T.begin database) reply after →
      RequestStep (preparationState request (PreparationRecovery.running events
        (PreparationRecovery.E.done (embedDocumentInput path chunks , inj₂ vectors)) prefix))
        (documentPublicationEffect (Document.T.begin database)) reply before after
    preparedDocumentClear : ∀ {request events path resolution prefix reply before after} →
      DocumentClearRecovery.Atomic (clearDocumentPath path resolution) before (Document.T.begin database) reply after →
      RequestStep (preparationState request (PreparationRecovery.running events
        (PreparationRecovery.E.done (canonicalClearInput path , resolution)) prefix))
        (documentClearEffect (Document.T.begin database)) reply before after
    learningPreparationRead : ∀ {q state effect reply before after} →
      LearningRecovery.PreparationAtomic q before effect reply after →
      RequestStep state (learningPreparationEffect q effect) reply before after
    learningCommitStep : ∀ {state q tx proposed value reply before after} →
      LearningRecovery.Commit.Atomic q tx proposed value before tt reply after →
      RequestStep state (learningCommitEffect q tx proposed value) reply before after
    preparedPosteriorStep : ∀ {request writes result successful events prefix reply before after} →
      PosteriorRecovery.Atomic writes result successful before tt reply after →
      RequestStep (preparingInference request (InferencePreparationRecovery.running events
        (InferencePreparationRecovery.E.done (Inference.publish (Inference.update writes result successful))) prefix))
        (inferenceEffect (Inference.persistBeta writes)) reply before after
    preparedSweepStep : ∀ {request ids events prefix reply before after} →
      Sweep.Certified.Atomic ids before (Sweep.S.begin database) reply after →
      RequestStep (preparingInference request (InferencePreparationRecovery.running events
        (InferencePreparationRecovery.E.done (Inference.publish (Inference.removeSelection ids))) prefix))
        (sweepEffect (Sweep.S.begin database)) reply before after
    posteriorStep : ∀ {writes result successful events continuation prefix reply before after} →
      PosteriorRecovery.Atomic writes result successful before tt reply after →
      RequestStep (publishingPosteriors writes result successful
        (PosteriorRecovery.R.running {writes = writes} {result = result} {successful = successful} events
          (PosteriorRecovery.R.E.ask {writes = writes} {result = result} {successful = successful} tt continuation) prefix))
        (inferenceEffect (Inference.persistBeta writes)) reply before after
    sweepStep : ∀ {ids events effect continuation prefix reply before after} →
      Sweep.Certified.Atomic ids before effect reply after →
      RequestStep (sweeping ids (Sweep.Certified.R.running {ids = ids} events
        (Sweep.S.E.ask effect continuation) prefix)) (sweepEffect effect) reply before after
    deletionStep : ∀ {kind id events effect continuation prefix reply before after} →
      DeleteRecovery.Atomic kind id before effect reply after →
      RequestStep (deleteState kind id (DeleteRecovery.R.running {kind = kind} {id = id} events
        (Delete.T.E.ask effect continuation) prefix)) (deleteEffect effect) reply before after
    groundingStep : ∀ {request events effect continuation prefix reply before after} →
      GroundRecovery.Atomic request before effect reply after →
      RequestStep (groundState request (GroundRecovery.R.running {request = request} events
        (Grounding.T.E.ask effect continuation) prefix)) (groundEffect effect) reply before after
    documentClearStep : ∀ {path events effect continuation prefix reply before after} →
      DocumentClearRecovery.Atomic path before effect reply after →
      RequestStep (clearingDocument path (DocumentClearRecovery.R.running {path = path} events
        (Document.T.E.ask effect continuation) prefix)) (documentClearEffect effect) reply before after
    documentPublicationStep : ∀ {path chunks vectors events effect continuation prefix reply before after} →
      DocumentReplaceRecovery.Atomic path chunks vectors before effect reply after →
      RequestStep (publishingDocument path chunks vectors
        (DocumentReplaceRecovery.R.running {path = path} {chunks = chunks} {vectors = vectors} events
          (Document.T.E.ask effect continuation) prefix)) (documentPublicationEffect effect) reply before after
    canonicalDocumentRead : ∀ {state path reply before} →
      RequestStep state (documentEffect (Document.canonicalize path)) reply before before
    documentFileRead : ∀ {state path reply before} →
      RequestStep state (documentEffect (Document.readUTF8 path)) reply before before
    documentEmbeddingRead : ∀ {state texts reply before} →
      RequestStep state (documentEffect (Document.embed texts)) reply before before
    other : ∀ {state effect reply before after} → Ordinary effect →
      RequestStep state effect reply before after
    graphRead : ∀ {state effect reply before} →
      RequestStep state (readEffect effect) reply before before
    learningRead : ∀ {state effect reply before} →
      RequestStep state (queryEffect effect) reply before before
    evidenceRead : ∀ {state effect reply before} →
      RequestStep state (evidenceEffect effect) reply before before
    documentSearchRead : ∀ {state effect reply before} →
      RequestStep state (documentQueryEffect effect) reply before before
    searchRead : ∀ {state effect reply before} →
      RequestStep state (searchEffect effect) reply before before
    contextRead : ∀ {state effect reply before} →
      RequestStep state (contextEffect effect) reply before before
    inferenceQueryRead : ∀ {state effect reply before} →
      RequestStep state (inferenceQueryEffect effect) reply before before
    inferencePreparationRead : ∀ {state effect reply before} →
      RequestStep state (inferencePreparationEffect effect) reply before before
    relationFailed : ∀ {state command detail before} →
      OrdinaryRelation command →
      RequestStep state (mutationEffect (Mutation.statement command)) (inj₁ detail) before before
    relationPublished : ∀ {state command receipt before after} →
      OrdinaryRelation command → Mutation.StatementReceipt command before receipt after →
      RequestStep state (mutationEffect (Mutation.statement command)) (inj₂ receipt) before after
    defeatFailed : ∀ {state from to weight detail before} →
      RequestStep state (mutationEffect (Mutation.recordDefeat from to weight)) (inj₁ detail) before before
    defeatPublished : ∀ {state from to weight receipt before after} →
      Mutation.DefeatReceipt from to weight before receipt after →
      RequestStep state (mutationEffect (Mutation.recordDefeat from to weight)) (inj₂ receipt) before after
    beliefPreparationNeedsInput : ∀ {state proposal reason guidance before} →
      RequestStep state (mutationEffect (Mutation.embedding (BeliefEmbedding.prepare proposal)))
        (BeliefEmbedding.askUser reason guidance) before before
    beliefPreparationReady : ∀ {state proposal material before} →
      BeliefEmbedding.Prepared.supportingPassage material ∈ Store.World.chunks before →
      RequestStep state (mutationEffect (Mutation.embedding (BeliefEmbedding.prepare proposal)))
        (BeliefEmbedding.ready material) before before
    beliefPublicationFailed : ∀ {state proposal material error before} →
      RequestStep state (mutationEffect (Mutation.embedding (BeliefEmbedding.publish proposal material)))
        (inj₁ error) before before
    beliefPublicationSucceeded : ∀ {state proposal material belief before after} →
      BeliefPublished proposal material belief before after →
      RequestStep state (mutationEffect (Mutation.embedding (BeliefEmbedding.publish proposal material)))
        (inj₂ belief) before after
    patternPublicationFailed : ∀ {state situation approach success project error before} →
      RequestStep state (mutationEffect (Mutation.createPattern situation approach success project))
        (inj₁ error) before before
    patternPublicationSucceeded : ∀ {state situation approach success project patternValue before after} →
      PatternPublished situation approach success project patternValue before after →
      RequestStep state (mutationEffect (Mutation.createPattern situation approach success project))
        (inj₂ patternValue) before after
    staging : ∀ {state effect reply before} → ForgetStaging effect →
      RequestStep state (forgetEffect effect) reply before before
    readFailed : ∀ {state tx failure before} →
      RequestStep state (forgetEffect (Forget.learning (Forget.T.read tx))) (inj₁ failure) before before
    readWorld : ∀ {state tx before} →
      RequestStep state (forgetEffect (Forget.learning (Forget.T.read tx))) (inj₂ before) before before
    committedCertifiedDeletion : ∀ {project events tx continuation prefix reply before after} →
      events ≡
        (Forget.learning (Forget.T.begin database) , inj₂ tx) ∷
        (Forget.learning (Forget.T.acquire tx 671942183) , inj₂ tt) ∷
        (Forget.learning (Forget.T.read tx) , inj₂ before) ∷
        (Forget.learning (Forget.T.write tx (Project.published project before)) , inj₂ tt) ∷ [] →
      DB.Atomic before (Project.published project before) (Forget.T.receipt reply) after →
      RequestStep
        (standaloneForgetState project (Standalone.R.running events
          (Forget.E.ask (Forget.learning (Forget.T.commit tx)) continuation) prefix))
        (forgetEffect (Forget.learning (Forget.T.commit tx))) reply before after
    committedCertifiedRequestDeletion : ∀ {identityValue project events tx continuation prefix reply before after} →
      events ≡
        (Forget.learning (Forget.T.begin database) , inj₂ tx) ∷
        (Forget.learning (Forget.T.acquire tx 671942183) , inj₂ tt) ∷
        (Forget.learning (Forget.T.read tx) , inj₂ before) ∷
        (Forget.learning (Forget.T.write tx (Project.published project before)) , inj₂ tt) ∷ [] →
      DB.Atomic before (Project.published project before) (Forget.T.receipt reply) after →
      RequestStep
        (requestState identityValue (standaloneForgetState project (Standalone.R.running events
          (Forget.E.ask (Forget.learning (Forget.T.commit tx)) continuation) prefix)))
        (forgetEffect (Forget.learning (Forget.T.commit tx))) reply before after

  beliefPreparationPreservesStore : ∀ {state proposal reply before after} →
    RequestStep state (mutationEffect (Mutation.embedding (BeliefEmbedding.prepare proposal))) reply before after →
    after ≡ before
  beliefPreparationPreservesStore (other ())
  beliefPreparationPreservesStore (underRequest step) = beliefPreparationPreservesStore step
  beliefPreparationPreservesStore beliefPreparationNeedsInput = refl
  beliefPreparationPreservesStore (beliefPreparationReady indexed) = refl

  failedBeliefPublicationPreservesStore : ∀ {state proposal material error before after} →
    RequestStep state (mutationEffect (Mutation.embedding (BeliefEmbedding.publish proposal material)))
      (inj₁ error) before after → after ≡ before
  failedBeliefPublicationPreservesStore (other ())
  failedBeliefPublicationPreservesStore (underRequest step) = failedBeliefPublicationPreservesStore step
  failedBeliefPublicationPreservesStore beliefPublicationFailed = refl

  failedPatternPublicationPreservesStore : ∀ {state situation approach success project error before after} →
    RequestStep state (mutationEffect (Mutation.createPattern situation approach success project))
      (inj₁ error) before after → after ≡ before
  failedPatternPublicationPreservesStore (other ())
  failedPatternPublicationPreservesStore (underRequest step) = failedPatternPublicationPreservesStore step
  failedPatternPublicationPreservesStore patternPublicationFailed = refl

  data GuardedRuns : State → Store.World → List Event → Store.World → Result → Set where
    returned : ∀ state store result → next state ≡ complete result → GuardedRuns state store [] store result
    replied : ∀ state effect continuation reply before middle events after result →
      next state ≡ perform effect continuation → RequestStep state effect reply before middle →
      GuardedRuns (continuation reply) middle events after result →
      GuardedRuns state before ((effect , reply) ∷ events) after result

  guardedExecution : ∀ {state before events after result} → GuardedRuns state before events after result → Runs state events result
  guardedExecution (returned state store result done) = returned state result done
  guardedExecution (replied state effect continuation reply before middle events after result nextStep receipt rest) =
    replied state effect continuation reply events result nextStep (guardedExecution rest)

  data Prefix : State → List Event → State → Set where
    stopped : ∀ state → Prefix state [] state
    replied : ∀ state effect continuation reply events residual →
      next state ≡ perform effect continuation → Prefix (continuation reply) events residual →
      Prefix state ((effect , reply) ∷ events) residual

  correctionHasNoEffects : ∀ fault events observed → Runs (correcting fault) events observed →
    events ≡ [] × observed ≡ admissionResult fault
  correctionHasNoEffects fault events observed (returned state result₁ refl) = refl , refl
