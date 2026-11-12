{-# OPTIONS --safe #-}
-- Exhaustive result classification and JSON projection. Failed/uncertain
-- operations remain errors even if an earlier component committed. The error
-- retains its complete typed cause for the host's diagnostic formatter.
module Mimir.ApplicationOutput where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Mimir.UUIDGroups using (UUID)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.String using (String; toList)
open import Mimir.Text using (Text)
import Mimir.StructuredValue as V
import Mimir.PublicEncoding as Encoding
import Mimir.ApplicationProtocol as Application
import Mimir.GraphMutationProtocol as Mutation
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
import Mimir.LearningContext as Context
import Mimir.LearningContextProtocol as ContextProtocol
import Mimir.AssessmentRead as Assessment
import Mimir.AssessmentSelection as Selection
import Mimir.AssessmentEvaluation as Evaluation
import Mimir.AssessmentScores as Scores
import Mimir.LearningCapabilities as Capabilities

module Project (environment : Application.Environment) (format : Encoding.Formatting) where
  module A = Application.Run environment
  open Encoding
  open Encode format

  data Projection : Set where
    success : V.Value → Projection
    failure : A.Result → Projection

  flag : String → Bool → V.Value
  flag fieldKey value = object ((fieldKey , V.boolean value) ∷ [])
  count : String → ℕ → V.Value
  count fieldKey value = object ((fieldKey , V.unsigned value) ∷ [])

  provenance : Provenance.Provenance → V.Value
  provenance p = object (("experience_id" , uuid (Provenance.Provenance.experienceID p)) ∷
    ("candidate_key" , V.string (Provenance.Provenance.candidateKey p)) ∷
    ("kind" , V.string (kind (Provenance.Provenance.kind p))) ∷
    ("active" , V.boolean (Provenance.Provenance.active p)) ∷ ("retired" , V.boolean (Provenance.Provenance.retired p)) ∷ [])
    where
    kind : Provenance.Kind → Text
    kind Provenance.beliefKind = toList "belief"
    kind Provenance.patternKind = toList "pattern"

  independent : Origin.Read → V.Value
  independent Origin.noProvenance = V.null
  independent Origin.malformed = V.null -- classified as failure before success projection
  independent (Origin.found p) = object (("basis" , V.string (basis (Origin.Provenance.basis p))) ∷
    ("reference" , V.string (Origin.Provenance.reference p)) ∷ [])
    where
    basis : Origin.Basis → Text
    basis Origin.userInstruction = toList "user_instruction"
    basis Origin.document = toList "document"

  incoming : Explain.Incoming → V.Value
  incoming p = object (("from_id" , uuid (Edges.Edge.from e)) ∷ ("to_id" , uuid (Edges.Edge.to e)) ∷
    ("relation" , V.string (relationText (Edges.Edge.relation e))) ∷ ("weight" , V.floating (Edges.Edge.weight e)) ∷
    ("source_probability" , real (Explain.Incoming.sourceProbability p)) ∷ [])
    where e = Explain.Incoming.edge p

  explanation : Explain.Explanation → V.Value
  explanation e = object (("belief" , belief (Explain.Explanation.belief e)) ∷
    ("incoming_edges" , V.array (map incoming (Explain.Explanation.incomingEdges e))) ∷
    ("learning" , object (("reviews" , V.array (map review (Explain.Page.entries page))) ∷
      ("total" , V.unsigned (Explain.Page.total page)) ∷ ("next_offset" , optional V.unsigned (Explain.Page.nextOffset page)) ∷ [])) ∷
    ("candidate_provenance" , optional provenance (Explain.Explanation.candidateProvenance e)) ∷
    ("independent_provenance" , independent (Explain.Explanation.independentProvenance e)) ∷ [])
    where page = Explain.Explanation.learning e

  currentReview : History.CurrentReview → V.Value
  currentReview r = object (("experience_id" , uuid (Experience.Experience.identity (Observation.Snapshot.experience s))) ∷
    ("revision" , V.signed (Observation.Snapshot.revision s)) ∷ ("review_revision" , V.signed (Observation.Snapshot.reviewRevision s)) ∷
    ("reviewed_revision" , V.signed (Observation.Snapshot.reviewedRevision s)) ∷
    ("review" , optional review (History.CurrentReview.applied r)) ∷ [])
    where s = History.CurrentReview.state r

  evaluation : Evaluation.Result → Maybe V.Value
  evaluation Evaluation.invalidStoredNumber = nothing
  evaluation (Evaluation.scored (Scores.rejected why)) = nothing
  evaluation (Evaluation.scored (Scores.accepted s)) = just (scores s)

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
  projectRead original (Read.paged p) = success (object (("beliefs" , V.array (map belief (Records.Page.beliefs p))) ∷
    ("total" , V.unsigned (Records.Page.total p)) ∷ ("offset" , V.unsigned (Records.Page.offset p)) ∷
    ("next_offset" , optional V.unsigned (Records.Page.nextOffset p)) ∷ []))
  projectRead original (Read.explained e) = success (explanation e)
  projectRead original (Read.counted value) = success value
  projectRead original (Read.failed error) = failure original
  projectRead original Read.invalidPage = failure original
  projectRead original Read.missingBelief = failure original
  projectRead original Read.invalidProvenance = failure original

  rawCurrent : UUID → RawHistory.Current → V.Value
  rawCurrent id currentRecord = object (("experience_id" , uuid id) ∷
    ("revision" , V.signed (RawHistory.Current.revision currentRecord)) ∷
    ("review_revision" , V.signed (RawHistory.Current.reviewRevision currentRecord)) ∷
    ("reviewed_revision" , V.signed (RawHistory.Current.reviewedRevision currentRecord)) ∷
    ("review" , optional (λ value → value) (RawHistory.Current.review currentRecord)) ∷ [])

  rawHistoryEntry : RawHistory.Entry → V.Value
  rawHistoryEntry storedEntry = object (("revision" , V.signed (RawHistory.Entry.revision storedEntry)) ∷
    ("payload" , RawHistory.Entry.payload storedEntry) ∷ ("created_at" , timestamp (RawHistory.Entry.createdAt storedEntry)) ∷ [])

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
  ... | just s = success (object (("project" , V.string (Selection.Query.project q)) ∷ ("belief_id" , uuid (Selection.Query.belief q)) ∷
    ("scope" , V.string (Selection.Query.scope q)) ∷ ("rubric" , V.string (Selection.Query.rubric q)) ∷ ("scores" , s) ∷ []))
  projectQuery original (Query.assessmentHistoryResult (Assessment.found p)) = success (object
    (("entries" , V.array (map assessmentEntry (Assessment.Page.entries p))) ∷
    ("next_offset" , optional V.unsigned (Assessment.Page.nextOffset p)) ∷ []))
  projectQuery original _ = failure original

  project : A.Result → Projection
  project (A.mutated (Mutation.insertedBelief b)) = success (belief b)
  project (A.mutated (Mutation.insertedPattern p)) = success (patternValue p)
  project (A.mutated Mutation.edgeInserted) = success (flag "ok" true)
  project original@(A.mutated _) = failure original
  project original@(A.readResult result) = projectRead original result
  project (A.deleted (A.Delete.T.applied value)) = success (flag "deleted" value)
  project (A.deleted (A.Delete.T.replayed value cleanup)) = success (flag "deleted" value)
  project original@(A.deleted _) = failure original
  project (A.forgotten (A.Forget.deleted n)) = success (count "deleted" n)
  project original@(A.forgotten _) = failure original
  project (A.inferred (Inference.propagated writes false)) = success (V.array (map (λ { (id , p) →
    object (("id" , uuid id) ∷ ("new_probability" , real p) ∷ []) }) writes))
  project (A.inferred (Inference.projected writes false)) = success (V.array (map (λ { (id , p) →
    object (("id" , uuid id) ∷ ("projected_probability" , real p) ∷ []) }) writes))
  project (A.inferred (Inference.changed n)) = success (count "decayed" n)
  project (A.inferred (Inference.deleted n)) = success (count "deleted" n)
  project (A.inferred (Inference.pairs pairs)) = success (V.array (map (λ { (a , b) → V.array (uuid a ∷ uuid b ∷ []) }) pairs))
  project original@(A.inferred _) = failure original
  project (A.swept (A.Sweep.S.applied n)) = success (count "deleted" n)
  project (A.swept (A.Sweep.S.replayed n cleanup)) = success (count "deleted" n)
  project original@(A.swept _) = failure original
  project (A.grounded (A.Grounding.T.applied tt)) = success (flag "ok" true)
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
  project original@(A.learned q _) = failure original
  project original@(A.learningQueryResult result) = projectQuery original result
  project original@(A.contextResult result) with contextAssessments (Context.Assessments.values (ContextProtocol.Output.assessments result))
  ... | nothing = failure original
  ... | just assessments = success (object (("beliefs" , V.array (map belief (ContextProtocol.Output.beliefs result))) ∷
    ("patterns" , V.array (ContextProtocol.Output.patterns result)) ∷ ("assessments" , V.array assessments) ∷
    ("assessments_truncated" , V.boolean (Context.Assessments.truncated (ContextProtocol.Output.assessments result))) ∷ []))
  project (A.capabilitiesResult c) = success (Capabilities.encode c)
  project original@(A.failed _) = failure original
  project original@(A.needsDecision _ _) = failure original
  project original@A.invalidRequestIdentity = failure original
  project original@A.invalidContext = failure original
  project original@A.invalidAssessment = failure original
