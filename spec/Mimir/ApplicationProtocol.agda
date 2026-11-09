{-# OPTIONS --safe #-}
-- Concrete dispatch for every public application request. Subprotocols retain
-- their typed effects, failures and commit receipts. Retrieval is a transition
-- system because concurrent data can grow; no arbitrary traversal fuel is used.
module Mimir.ApplicationProtocol where

open import Data.Bool using (Bool; true; false)
open import Data.Float.Base using (Float)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.PublicRequest as Public
import Mimir.GraphMutationProtocol as Mutation
import Mimir.GraphReadProtocol as Read
import Mimir.GraphDeletion as Deletion
import Mimir.ProjectDeletion as Project
import Mimir.InferenceProtocol as Inference
import Mimir.GroundingPublication as Ground
import Mimir.EvidenceRead as Evidence
import Mimir.DocumentLoading as Documents
import Mimir.DocumentQuery as DocumentQuery
import Mimir.RetrievalProtocol as Retrieval
import Mimir.RetrievalRanking as Ranking
import Mimir.LearningContextProtocol as Context
import Mimir.LearningOperations as Learning
import Mimir.LearningQueryProtocol as Query
import Mimir.LearningCandidates as Candidates
import Mimir.LearningCapabilities as Capabilities
import Mimir.CandidateGraph as Graph
import Mimir.Effects as Effects
import Mimir.Validation as Validation
import Mimir.McpErrors as Errors
module Correction = Errors.AgentCorrection

configurationCorrection : Validation.Fault → Correction.Claim
configurationCorrection detail = Correction.claim
  (Correction.item Correction.configuration detail
    (toList "A user-chosen retirement.grace_hours value in Mimir configuration.")
    (toList "Ask the user to choose or repair the configured retention period. Do not send a per-call override or guess a default.")) []

record Environment : Set₁ where
  field
    database dimension : ℕ
    embeddingsEnabled : Bool
    f32 : Ranking.F32
    unicode : Ranking.Unicode
    databaseTextBefore : Text → Text → Bool
    now : ℤ
    retirementPolicy : Validation.Fault ⊎ ℤ
    candidateClock : Candidates.Candidate → ℤ
    candidateIdentity : Candidates.Candidate → ℕ
    chunkIdentity : ℕ → ℕ

module Run (environment : Environment) where
  open Environment environment
  module Delete = Deletion.Operation database
  module Forget = Project.Operation database
  module Grounding = Ground.Operation database
  module Document = Documents.Operations database dimension
  module Learn (q : Learning.Request) = Learning.Protocol database q candidateClock now candidateIdentity
  module Retrieve = Retrieval.Run f32 unicode
  module LearningContext = Context.Run f32 unicode databaseTextBefore

  admission : Public.Request → Validation.Fault ⊎ ⊤
  admission (Public.sweepConfigured project threshold) with retirementPolicy
  ... | inj₁ detail = inj₁ detail
  ... | inj₂ period = inj₂ tt
  admission _ = inj₂ tt

  missingPolicyRefusesAdmission : ∀ project threshold detail → retirementPolicy ≡ inj₁ detail →
    admission (Public.sweepConfigured project threshold) ≡ inj₁ detail
  missingPolicyRefusesAdmission project threshold detail missing rewrite missing = refl

  data Result : Set where
    mutated : Mutation.Result → Result
    readResult : Read.Result → Result
    deleted : Delete.T.Outcome → Result
    forgotten : Forget.Result → Result
    inferred : Inference.Result → Result
    grounded : Grounding.T.Outcome → Result
    invalidGrounding : Result
    evidenceResult : Text ⊎ List Evidence.Reference → Result
    relevantResult : Retrieval.Report → Result
    groundedResult : Retrieval.Coverage → Text ⊎ List Evidence.Grounded → Result
    documentResult : Document.Result → Result
    documentQueryResult : DocumentQuery.Result → Result
    learned : (q : Learning.Request) → Learn.Outcome q → Result
    learningQueryResult : Query.Result → Result
    contextResult : Context.Output → Result
    capabilitiesResult : Capabilities.Capabilities → Result
    failed : Text → Result
    invalidContext invalidAssessment : Result

  data State : Set where
    finished : Result → State
    mutationState : Mutation.E.Script Mutation.Result → State
    readState : Read.E.Script Read.Result → State
    deleteState : Delete.T.E.Script Delete.T.Outcome → State
    forgetState : Forget.E.Script Forget.Result → State
    inferenceState : Inference.E.Script Inference.Result → State
    groundState : Grounding.T.E.Script Grounding.T.Outcome → State
    evidenceState : Evidence.E.Script (Text ⊎ List Evidence.Reference) → State
    groundedState : Retrieval.Coverage → Evidence.E.Script (Text ⊎ List Evidence.Grounded) → State
    documentState : Document.E.Script Document.Result → State
    documentQueryState : DocumentQuery.E.Script DocumentQuery.Result → State
    learningState : (q : Learning.Request) → Learn.E.Script q (Learn.Outcome q) → State
    queryState : Query.E.Script Query.Result → State
    retrievalState : Bool → Ranking.Selection → Retrieval.State → State
    contextState : Context.State → State

  data Effect : Set where
    mutationEffect : Mutation.Effect → Effect
    readEffect : Read.Effect → Effect
    deleteEffect : Delete.T.Effect → Effect
    forgetEffect : Forget.Effect → Effect
    inferenceEffect : Inference.Effect → Effect
    groundEffect : Grounding.T.Effect → Effect
    evidenceEffect : Evidence.Effect → Effect
    documentEffect : Document.Effect → Effect
    documentQueryEffect : DocumentQuery.Effect → Effect
    learningEffect : (q : Learning.Request) → Learn.Effect q → Effect
    queryEffect : Query.Effect → Effect
    retrievalEffect : Retrieval.State → Effect
    contextEffect : Context.State → Effect

  Reply : Effect → Set
  Reply (mutationEffect e) = Mutation.Reply e
  Reply (readEffect e) = Read.Reply e
  Reply (deleteEffect e) = Delete.T.Reply e
  Reply (forgetEffect e) = Forget.Reply e
  Reply (inferenceEffect e) = Inference.Reply e
  Reply (groundEffect e) = Grounding.T.Reply e
  Reply (evidenceEffect e) = Evidence.Reply e
  Reply (documentEffect e) = Document.Reply e
  Reply (documentQueryEffect e) = DocumentQuery.Reply e
  Reply (learningEffect q e) = Learn.Reply q e
  Reply (queryEffect e) = Query.Reply e
  Reply (retrievalEffect s) = Retrieval.Reply s
  Reply (contextEffect s) = Context.Reply s

  data Next : Set where
    complete : Result → Next
    perform : (effect : Effect) → (Reply effect → State) → Next

  groundedNext : Retrieval.Coverage → Evidence.E.Script (Text ⊎ List Evidence.Grounded) → Next
  groundedNext observedCoverage (Evidence.E.done result) = complete (groundedResult observedCoverage result)
  groundedNext observedCoverage (Evidence.E.ask e k) = perform (evidenceEffect e) (λ r → groundedState observedCoverage (k r))

  next : State → Next
  next (finished result) = complete result
  next (mutationState (Mutation.E.done result)) = complete (mutated result)
  next (mutationState (Mutation.E.ask e k)) = perform (mutationEffect e) (λ r → mutationState (k r))
  next (readState (Read.E.done result)) = complete (readResult result)
  next (readState (Read.E.ask e k)) = perform (readEffect e) (λ r → readState (k r))
  next (deleteState (Delete.T.E.done result)) = complete (deleted result)
  next (deleteState (Delete.T.E.ask e k)) = perform (deleteEffect e) (λ r → deleteState (k r))
  next (forgetState (Forget.E.done result)) = complete (forgotten result)
  next (forgetState (Forget.E.ask e k)) = perform (forgetEffect e) (λ r → forgetState (k r))
  next (inferenceState (Inference.E.done result)) = complete (inferred result)
  next (inferenceState (Inference.E.ask e k)) = perform (inferenceEffect e) (λ r → inferenceState (k r))
  next (groundState (Grounding.T.E.done result)) = complete (grounded result)
  next (groundState (Grounding.T.E.ask e k)) = perform (groundEffect e) (λ r → groundState (k r))
  next (evidenceState (Evidence.E.done result)) = complete (evidenceResult result)
  next (evidenceState (Evidence.E.ask e k)) = perform (evidenceEffect e) (λ r → evidenceState (k r))
  next (groundedState observedCoverage (Evidence.E.done result)) = complete (groundedResult observedCoverage result)
  next (groundedState observedCoverage (Evidence.E.ask e k)) = perform (evidenceEffect e) (λ r → groundedState observedCoverage (k r))
  next (documentState (Document.E.done result)) = complete (documentResult result)
  next (documentState (Document.E.ask e k)) = perform (documentEffect e) (λ r → documentState (k r))
  next (documentQueryState (DocumentQuery.E.done result)) = complete (documentQueryResult result)
  next (documentQueryState (DocumentQuery.E.ask e k)) = perform (documentQueryEffect e) (λ r → documentQueryState (k r))
  next (learningState q (Learn.E.done result)) = complete (learned q result)
  next (learningState q (Learn.E.ask e k)) = perform (learningEffect q e) (λ r → learningState q (k r))
  next (queryState (Query.E.done result)) = complete (learningQueryResult result)
  next (queryState (Query.E.ask e k)) = perform (queryEffect e) (λ r → queryState (k r))
  next (retrievalState false per (Retrieval.finished result)) = complete (relevantResult result)
  next (retrievalState true per (Retrieval.finished result)) = groundedNext (Retrieval.Report.retrieval result)
    (Evidence.many per (Retrieval.Report.beliefs result))
  next (retrievalState include per (Retrieval.failed error)) = complete (failed error)
  next (retrievalState include per s@(Retrieval.overlay _)) = perform (retrievalEffect s) (λ r → retrievalState include per (Retrieve.advance s r))
  next (retrievalState include per s@(Retrieval.beliefs _ _)) = perform (retrievalEffect s) (λ r → retrievalState include per (Retrieve.advance s r))
  next (retrievalState include per s@(Retrieval.embedding _ _ _ _)) = perform (retrievalEffect s) (λ r → retrievalState include per (Retrieve.advance s r))
  next (retrievalState include per s@(Retrieval.vectorQuery _ _ _ _ _)) = perform (retrievalEffect s) (λ r → retrievalState include per (Retrieve.advance s r))
  next (retrievalState include per s@(Retrieval.closure _ _ _)) = perform (retrievalEffect s) (λ r → retrievalState include per (Retrieve.advance s r))
  next (retrievalState include per s@(Retrieval.neighbors _ _ _ _ _ _)) = perform (retrievalEffect s) (λ r → retrievalState include per (Retrieve.advance s r))
  next (contextState (Context.finished result)) = complete (contextResult result)
  next (contextState (Context.failed error)) = complete (failed error)
  next (contextState Context.invalidInput) = complete invalidContext
  next (contextState Context.invalidAssessment) = complete invalidAssessment
  next (contextState s@(Context.opening _)) = perform (contextEffect s) (λ r → contextState (LearningContext.advance s r))
  next (contextState s@(Context.owned _ _)) = perform (contextEffect s) (λ r → contextState (LearningContext.advance s r))
  next (contextState s@(Context.closing _ _)) = perform (contextEffect s) (λ r → contextState (LearningContext.advance s r))
  next (contextState s@(Context.retrieving _ _)) = perform (contextEffect s) (λ r → contextState (LearningContext.advance s r))
  next (contextState s@(Context.listPatterns _ _)) = perform (contextEffect s) (λ r → contextState (LearningContext.advance s r))
  next (contextState s@(Context.countPattern _ _ _ _ _ _)) = perform (contextEffect s) (λ r → contextState (LearningContext.advance s r))
  next (contextState s@(Context.patternOrigin _ _ _ _ _ _)) = perform (contextEffect s) (λ r → contextState (LearningContext.advance s r))
  next (contextState s@(Context.assessmentGroups _ _ _)) = perform (contextEffect s) (λ r → contextState (LearningContext.advance s r))

  groundStart : ℕ → ℕ → Float → State
  groundStart belief chunk weight with Grounding.Run.start (Ground.add chunk belief weight)
  ... | nothing = finished invalidGrounding
  ... | just program = groundState program

  preference : Bool → Maybe Candidates.Memory → Maybe Candidates.Memory
  preference false requested = requested
  preference true requested = nothing -- current grounded-service path ignores prefer_type

  start : Public.Request → State
  start (Public.mutation q) = mutationState (Mutation.start embeddingsEnabled q)
  start (Public.read q) = readState (Read.start q)
  start (Public.delete kind id) = deleteState (Delete.Run.start kind id)
  start (Public.deleteProject project) = forgetState (Forget.start project)
  start (Public.inference q) = inferenceState (Inference.start q)
  start (Public.sweepConfigured project threshold) with retirementPolicy
  ... | inj₁ detail = finished (failed (Validation.Fault.explanation detail))
  ... | inj₂ period = inferenceState (Inference.start (Inference.sweep project threshold period))
  start (Public.relevant query limit project prefer include per) = retrievalState include per
    (Retrieval.overlay (Retrieval.request query limit project (preference include prefer) embeddingsEnabled))
  start (Public.addEvidence belief chunk weight) = groundStart belief chunk weight
  start (Public.removeEvidence belief chunk) = groundState (Grounding.Run.P.start (Ground.remove chunk belief))
  start (Public.evidence belief) = evidenceState (Evidence.one belief nothing)
  start (Public.loadDocument path project) = documentState (Document.load embeddingsEnabled chunkIdentity path project)
  start (Public.queryDocument query project limit) = documentQueryState (DocumentQuery.start embeddingsEnabled query limit project)
  start (Public.clearDocument path) = documentState (Document.clear path)
  start (Public.learning q) = learningState q (Learn.start q)
  start (Public.learningQuery q) = queryState (Query.start q)
  start (Public.learningContext query project limit) = contextState
    (LearningContext.begin (Context.contextRequest query project limit embeddingsEnabled))
  start Public.capabilities = finished (capabilitiesResult Capabilities.current)

  Event = Σ Effect Reply

  data Runs : State → List Event → Result → Set where
    returned : ∀ state result → next state ≡ complete result → Runs state [] result
    replied : ∀ state effect continuation reply events result →
      next state ≡ perform effect continuation → Runs (continuation reply) events result →
      Runs state ((effect , reply) ∷ events) result

  data Prefix : State → List Event → State → Set where
    stopped : ∀ state → Prefix state [] state
    replied : ∀ state effect continuation reply events residual →
      next state ≡ perform effect continuation → Prefix (continuation reply) events residual →
      Prefix state ((effect , reply) ∷ events) residual

  finishedHasNoEffects : ∀ result events observed → Runs (finished result) events observed →
    events ≡ [] × observed ≡ result
  finishedHasNoEffects result events observed (returned state result₁ refl) = refl , refl
