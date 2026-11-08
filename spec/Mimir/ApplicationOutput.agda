{-# OPTIONS --safe #-}
-- Exhaustive result classification and JSON projection. Failed/uncertain
-- operations remain errors even if an earlier component committed. The error
-- retains its complete typed cause for the host's diagnostic formatter.
module Mimir.ApplicationOutput where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.String using (String; toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.StructuredValue as V
import Mimir.PublicEncoding as Encoding
import Mimir.ApplicationProtocol as Application
import Mimir.GraphMutationProtocol as Mutation
import Mimir.GroundingPublication as Ground
import Mimir.GraphReadProtocol as Read
import Mimir.GraphRecords as Records
import Mimir.InferenceProtocol as Inference
import Mimir.DocumentQuery as DocumentQuery
import Mimir.LearningQueryProtocol as Query
import Mimir.LearningOperations as Operations
import Mimir.LearningHistory as History
import Mimir.LearningHistoryWire as RawHistory
import Mimir.ExperienceRead as Experiences
import Mimir.ReviewObservation as Observation
import Mimir.ExperienceSchema as Experience
import Mimir.BeliefExplanation as Explain
import Mimir.ReviewEdges as Edges
import Mimir.IndependentProvenance as Origin
import Mimir.CandidateProvenance as Provenance
import Mimir.PatternOutcomes as Pattern
import Mimir.LearningContext as Context
import Mimir.LearningContextProtocol as ContextProtocol
import Mimir.AssessmentRead as Assessment
import Mimir.AssessmentSelection as Selection
import Mimir.AssessmentEvaluation as Evaluation
import Mimir.AssessmentScores as Scores
import Mimir.LearningCapabilities as Capabilities
import Mimir.BeliefEmbedding as Embedding
import Mimir.McpErrors as Errors

module Project (environment : Application.Environment) (format : Encoding.Formatting) where
  module A = Application.Run environment
  open Encoding
  open Encode format

  data Projection : Set where
    success : V.Value → Projection
    failure : A.Result → Projection
    decision : Errors.AgentCorrection.Claim → Projection

  flag : String → Bool → V.Value
  flag fieldKey value = object ((fieldKey , V.boolean value) ∷ [])
  count : String → ℕ → V.Value
  count fieldKey value = object ((fieldKey , V.unsigned value) ∷ [])

  patternResult : Pattern.Result → V.Value
  patternResult p = object (("pattern" , patternValue (Pattern.Result.patternValue p)) ∷
    ("successes" , V.unsigned (Pattern.Counts.successes counts)) ∷ ("failures" , V.unsigned (Pattern.Counts.failures counts)) ∷
    ("unknown" , V.unsigned (Pattern.Counts.unknowns counts)) ∷
    ("observed_success_probability" , real (Pattern.Result.observedSuccessProbability p)) ∷ originField (Pattern.Result.candidateProvenance p))
    where
    counts = Pattern.Result.observations p
    originField : Maybe Provenance.Provenance → List (String × V.Value)
    originField nothing = []
    originField (just origin) = ("candidate_provenance" , provenance origin) ∷ []

  currentReview : History.CurrentReview → V.Value
  currentReview r = object (("experience_id" , uuid (Experience.Experience.identity (Observation.Snapshot.experience s))) ∷
    ("revision" , V.signed (Observation.Snapshot.revision s)) ∷ ("review_revision" , V.signed (Observation.Snapshot.reviewRevision s)) ∷
    ("reviewed_revision" , V.signed (Observation.Snapshot.reviewedRevision s)) ∷
    ("review" , optional review (History.CurrentReview.applied r)) ∷ [])
    where s = History.CurrentReview.state r

  contextAssessments : List (Context.Key × Evaluation.Result) → Maybe (List V.Value)
  contextAssessments [] = just []
  contextAssessments ((fieldKey , evaluated) ∷ rest) with evaluation evaluated | contextAssessments rest
  ... | just s | just later = just (object (("belief_id" , uuid (Context.Key.belief fieldKey)) ∷
    ("scope" , V.string (Context.Key.scope fieldKey)) ∷ ("rubric" , V.string (Context.Key.rubric fieldKey)) ∷ ("scores" , s) ∷ []) ∷ later)
  ... | _ | _ = nothing

  projectRead : A.Result → Read.Result → Projection
  projectRead original (Read.beliefResult b) = success (optional belief b)
  projectRead original (Read.patternResult p) = success (optional patternValue p)
  projectRead original (Read.beliefList bs) = success (V.array (map belief bs))
  projectRead original (Read.patternList ps) = success (V.array (map patternValue ps))
  projectRead original (Read.paged p) = success (beliefPage p)
  projectRead original (Read.explained e) = success (explanation e)
  projectRead original (Read.counted s) = success (object (("beliefs" , V.unsigned (Read.Statistics.beliefCount s)) ∷
    ("patterns" , V.unsigned (Read.Statistics.patternCount s)) ∷ ("supports" , V.unsigned (Read.Statistics.supportCount s)) ∷
    ("defeats" , V.unsigned (Read.Statistics.defeatCount s)) ∷ ("causes" , V.unsigned (Read.Statistics.causeCount s)) ∷
    ("contradicts" , V.unsigned (Read.Statistics.contradictionCount s)) ∷ []))
  projectRead original (Read.failed error) = failure original
  projectRead original Read.invalidPage = failure original
  projectRead original Read.missingBelief = failure original
  projectRead original Read.invalidProvenance = failure original

  projectQuery : A.Result → Query.Result → Projection
  projectQuery original (Query.experienceResult s) = success (optional snapshot s)
  projectQuery original (Query.reviewResult r) = success (optional currentReview r)
  projectQuery original (Query.rawReviewResult id r) = success (optional (rawCurrent id) r)
  projectQuery original (Query.rawHistoryResult sources reviews) = success (object
    (("experiences" , V.array (map rawHistoryEntry sources)) ∷ ("reviews" , V.array (map rawHistoryEntry reviews)) ∷ []))
  projectQuery original (Query.historyResult (History.history sources reviews)) = success (object
    (("experiences" , V.array (map (historyEntry experience) sources)) ∷
     ("reviews" , V.array (map (historyEntry review) reviews)) ∷ []))
  projectQuery original (Query.pendingResult (Experiences.selected ss)) = success (V.array (map snapshot ss))
  projectQuery original (Query.scoreResult (Assessment.assessed q result)) with evaluation result
  ... | nothing = failure original
  ... | just s = success (assessmentResult q s)
  projectQuery original (Query.assessmentHistoryResult (Assessment.found p)) = success (assessmentPage p)
  projectQuery original _ = failure original

  project : A.Result → Projection
  project (A.mutated (Mutation.insertedBelief b)) = success (belief b)
  project (A.mutated (Mutation.insertedPattern p)) = success (patternValue p)
  project (A.mutated Mutation.edgeInserted) = success (flag "ok" true)
  project (A.mutated (Mutation.needsInput report)) = decision report
  project (A.mutated (Mutation.embeddingFailed (Embedding.needsUserDecision report))) = decision report
  project original@(A.mutated _) = failure original
  project original@(A.readResult result) = projectRead original result
  project (A.deleted (A.Delete.T.applied value)) = success (flag "deleted" value)
  project (A.deleted (A.Delete.T.replayed value cleanup)) = success (flag "deleted" value)
  project original@(A.deleted _) = failure original
  project (A.forgotten (A.Forget.deleted n)) = success (count "deleted" n)
  project original@(A.forgotten _) = failure original
  project (A.inferred (Inference.propagated writes warning)) = success (V.array (map (λ { (id , p) →
    object (("id" , uuid id) ∷ ("new_probability" , real p) ∷ []) }) writes))
  project (A.inferred (Inference.projected writes warning)) = success (V.array (map (λ { (id , p) →
    object (("id" , uuid id) ∷ ("projected_probability" , real p) ∷ []) }) writes))
  project (A.inferred (Inference.changed n)) = success (count "decayed" n)
  project (A.inferred (Inference.deleted n)) = success (count "deleted" n)
  project (A.inferred (Inference.pairs pairs)) = success (V.array (map identityPair pairs))
  project (A.inferred Inference.missingBelief) = decision (Errors.AgentCorrection.claim
    (Errors.AgentCorrection.missingStoredReference "id" (Data.String.toList "The requested belief is not stored in Mimir.")
      (Data.String.toList "Use list_beliefs or query_relevant_beliefs to find the intended stored belief, then retry with its ID. If the intended record is unknown, ask the user. Do not invent an identifier.")) [])
  project original@(A.inferred _) = failure original
  project (A.grounded (A.Grounding.T.applied tt)) = success (flag "ok" true)
  project (A.grounded (A.Grounding.T.refused Ground.missingChunk (inj₂ tt))) = decision (Errors.AgentCorrection.claim
    (Errors.AgentCorrection.missingStoredReference "chunk_id" (Data.String.toList "The requested document passage is not stored in Mimir.")
      (Data.String.toList "Use query_document or list_documents to find the intended indexed passage. If the document is missing, ask the user whether to index it; do not invent a passage ID.")) [])
  project (A.grounded (A.Grounding.T.refused Ground.missingBelief (inj₂ tt))) = decision (Errors.AgentCorrection.claim
    (Errors.AgentCorrection.missingStoredReference "belief_id" (Data.String.toList "The requested belief is not stored in Mimir.")
      (Data.String.toList "Use list_beliefs or query_relevant_beliefs to find the intended stored belief, then retry with its ID. If the intended record is unknown, ask the user. Do not invent an identifier.")) [])
  project original@(A.grounded _) = failure original
  project original@A.invalidGrounding = failure original
  project (A.evidenceResult (inj₂ refs)) = success (V.array (map reference refs))
  project original@(A.evidenceResult (inj₁ error)) = failure original
  project (A.relevantResult beliefs) = success (V.array (map belief beliefs))
  project (A.groundedResult (inj₂ beliefs)) = success (V.array (map grounded beliefs))
  project original@(A.groundedResult (inj₁ error)) = failure original
  project (A.documentResult (A.Document.loaded n)) = success (count "loaded" n)
  project (A.documentResult (A.Document.cleared n)) = success (count "cleared" n)
  project original@(A.documentResult _) = failure original
  project (A.documentQueryResult (DocumentQuery.found hits)) = success (V.array (map documentHit hits))
  project original@(A.documentQueryResult _) = failure original
  project (A.learned q (A.Learn.transacted (A.Learn.T.applied s))) = success (snapshot s)
  project (A.learned q (A.Learn.transacted (A.Learn.T.replayed s cleanup))) = success (snapshot s)
  project (A.learned q (A.Learn.reviewTransacted (A.Learn.Full.applied s))) = success (snapshot s)
  project (A.learned q (A.Learn.reviewTransacted (A.Learn.Full.replayed s cleanup))) = success (snapshot s)
  project (A.learned q (A.Learn.preparationDecision report)) = decision report
  project (A.learned q (A.Learn.reviewTransacted (A.Learn.Full.refused (Operations.preparationFailure report) cleanup))) = decision report
  project original@(A.learned q (A.Learn.transacted (A.Learn.T.refused reason (inj₂ tt)))) with Operations.revisionCorrection reason
  ... | just report = decision report
  ... | nothing = failure original
  project original@(A.learned q (A.Learn.reviewTransacted (A.Learn.Full.refused reason (inj₂ tt)))) with Operations.revisionCorrection reason
  ... | just report = decision report
  ... | nothing = failure original
  project original@(A.learned q _) = failure original
  project original@(A.learningQueryResult result) = projectQuery original result
  project original@(A.contextResult result) with contextAssessments (Context.Assessments.values (ContextProtocol.Output.assessments result))
  ... | nothing = failure original
  ... | just assessments = success (object (("beliefs" , V.array (map belief (ContextProtocol.Output.beliefs result))) ∷
    ("patterns" , V.array (map patternResult (ContextProtocol.Output.patterns result))) ∷ ("assessments" , V.array assessments) ∷
    ("assessments_truncated" , V.boolean (Context.Assessments.truncated (ContextProtocol.Output.assessments result))) ∷ []))
  project (A.capabilitiesResult c) = success (Capabilities.encode c)
  project original@(A.failed _) = failure original
  project original@A.invalidContext = failure original
  project original@A.invalidAssessment = failure original

  -- A lost acknowledgement may have committed. Even when its error carries
  -- revision information, it cannot use the no-business-changes correction.
  module RevisionOutcomeLaws (q : Operations.Request) where
    module L = A.Learn q

    uncertainRecordRequiresReadback : ∀ value reason →
      project (A.learned q (L.transacted (L.T.commitUncertain value reason))) ≡
      failure (A.learned q (L.transacted (L.T.commitUncertain value reason)))
    uncertainRecordRequiresReadback value reason = refl

    uncertainReviewRequiresReadback : ∀ value reason →
      project (A.learned q (L.reviewTransacted (L.Full.commitUncertain value reason))) ≡
      failure (A.learned q (L.reviewTransacted (L.Full.commitUncertain value reason)))
    uncertainReviewRequiresReadback value reason = refl
