{-# OPTIONS --safe #-}
-- Application JSON field projections. UUID/RFC3339/IEEE scalar formatting is
-- a standard dependency boundary; object shape, omitted fields, nulls and
-- semantic values are concrete here. Nonfinite serde floats become JSON null.
module Mimir.PublicEncoding where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Float.Base using (Float; isNaN; isInfinite)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; toList)
open import Mimir.Text using (Text)
open import Mimir.UUIDGroups using (UUID)
import Mimir.StructuredValue as V
import Mimir.Binary64 as Binary
import Mimir.CandidateGraph as G
import Mimir.CandidateWire as Candidate
import Mimir.LearningCandidates as Declaration
import Mimir.SourceWire as Source
import Mimir.SourceReview as Coverage
import Mimir.ExperienceSchema as X
import Mimir.ReviewSchema as R
import Mimir.LearningSchema as L
import Mimir.NumericValidation as N
import Mimir.ReviewObservation as Observation
import Mimir.BeliefExplanation as Explain
import Mimir.IndependentProvenance as Origin
import Mimir.CandidateProvenance as Provenance
import Mimir.EvidenceRead as Evidence
import Mimir.DocumentQuery as Document
import Mimir.AssessmentScores as Scores
import Mimir.AssessmentRead as Assessment
import Mimir.AssessmentWrites as Contributions
import Mimir.LearningHistory as History

record Formatting : Set where
  field
    uuidText : UUID → Text -- lowercase canonical hyphenated UUID
    utcText : ℤ → Text -- chrono UTC RFC3339 of represented nanoseconds
    floatBits : Float → Binary.Number -- the same binary64 value, no rounding policy

object : List (String × V.Value) → V.Value
object fields = V.object (map (λ { (name , value) → toList name , value }) fields)

optional : ∀ {A : Set} → (A → V.Value) → Maybe A → V.Value
optional encode nothing = V.null
optional encode (just value) = encode value

presentField : ∀ {A : Set} → String → (A → V.Value) → Maybe A → List (String × V.Value)
presentField name encode nothing = []
presentField name encode (just value) = (name , encode value) ∷ []

nonempty : ∀ {A : Set} → String → (A → V.Value) → List A → List (String × V.Value)
nonempty name encode [] = []
nonempty name encode xs@(_ ∷ _) = (name , V.array (map encode xs)) ∷ []

relationText : R.Relation → Text
relationText R.supports = toList "Supports"
relationText R.defeats = toList "Defeats"
relationText R.causes = toList "Causes"
relationText R.contradicts = toList "Contradicts"

verdictText : R.Verdict → Text
verdictText R.support = toList "support"
verdictText R.defeat = toList "defeat"

outcomeText : X.Outcome → Text
outcomeText X.success = toList "success"
outcomeText X.failure = toList "failure"
outcomeText X.unknown = toList "unknown"

kindText : L.Kind → Text
kindText L.estimate = toList "estimate"
kindText L.decision = toList "decision"
kindText L.suggestion = toList "suggestion"

coverageText : Coverage.Status → Text
coverageText Coverage.complete = toList "complete"
coverageText Coverage.unresolved = toList "unresolved"

module Encode (format : Formatting) where
  uuid : UUID → V.Value
  uuid id = V.string (Formatting.uuidText format id)
  timestamp : ℤ → V.Value
  timestamp time = V.string (Formatting.utcText format time)
  real : Float → V.Value
  real value with isNaN value ∨ isInfinite value
  ... | true = V.null
  ... | false = V.floating (Formatting.floatBits format value)

  belief : G.BeliefValues → V.Value
  belief b = object
    (("id" , uuid (G.BeliefValues.identity b)) ∷ ("content" , V.string (G.BeliefValues.content b)) ∷
    ("probability" , real (G.BeliefValues.probability b)) ∷ ("confidence" , real (G.BeliefValues.confidence b)) ∷
    ("alpha" , real (G.BeliefValues.alpha b)) ∷ ("beta" , real (G.BeliefValues.beta b)) ∷
    ("alpha0" , real (G.BeliefValues.alpha0 b)) ∷ ("beta0" , real (G.BeliefValues.beta0 b)) ∷
    ("created_at" , timestamp (G.BeliefValues.created b)) ∷ ("last_activated_at" , timestamp (G.BeliefValues.activated b)) ∷
    ("memory_type" , V.string (Candidate.memoryText (G.BeliefValues.memory b))) ∷
    projectField (G.BeliefValues.project b))
    where
    projectField : Maybe Text → List (String × V.Value)
    projectField nothing = []
    projectField (just p) = ("project" , V.string p) ∷ []

  patternValue : G.PatternValues → V.Value
  patternValue p = object (("id" , uuid (G.PatternValues.identity p)) ∷
    ("situation" , V.string (G.PatternValues.situation p)) ∷ ("approach" , V.string (G.PatternValues.approach p)) ∷
    ("success_rate" , real (G.PatternValues.successRate p)) ∷ ("activation_count" , V.unsigned (G.PatternValues.activationCount p)) ∷
    ("created_at" , timestamp (G.PatternValues.created p)) ∷ ("project" , optional V.string (G.PatternValues.project p)) ∷ [])

  prediction : L.Prediction → V.Value
  prediction p = object (("quantity" , V.string (L.Prediction.quantity p)) ∷ ("value" , V.floating (L.Prediction.point p)) ∷
    ("unit" , V.string (L.Prediction.unit p)) ∷ ("probability" , optional V.floating (L.Prediction.probability p)) ∷
    ("lower" , optional V.floating (L.Prediction.lower p)) ∷ ("upper" , optional V.floating (L.Prediction.upper p)) ∷
    ("horizon" , V.string (L.Prediction.horizon p)) ∷ ("recorded_at" , V.string (L.Prediction.recordedAt p)) ∷
    ("inferred" , V.boolean (L.Prediction.inferred p)) ∷ [])

  item : L.LearningItem → V.Value
  item i = object (("id" , uuid (L.LearningItem.identity i)) ∷ ("kind" , V.string (kindText (L.LearningItem.kind i))) ∷
    ("key" , optional V.string (L.LearningItem.localKey i)) ∷
    ("source_ref" , V.string (L.LearningItem.reference i)) ∷ ("actor" , V.string (L.LearningItem.actor i)) ∷
    ("statement" , V.string (L.LearningItem.statement i)) ∷ ("conditions" , V.string (L.LearningItem.conditions i)) ∷
    ("predictions" , V.array (map prediction (L.LearningItem.predictions i))) ∷ [])

  target : L.Target → V.Value
  target (L.existing id) = object (("belief_id" , uuid id) ∷ [])
  target (L.candidate key) = object (("candidate_key" , V.string key) ∷ [])

  axis : N.Axis → V.Value
  axis a = object (("value" , optional V.floating (N.Axis.estimate a)) ∷ ("weight" , V.floating (N.Axis.weight a)) ∷ [])

  assessment : L.Assessment → V.Value
  assessment a = object (("target" , target (L.Assessment.target a)) ∷ ("scope" , V.string (L.Assessment.scope a)) ∷
    ("rubric" , V.string (L.Assessment.rubric a)) ∷ ("correctness" , axis (L.Assessment.correctness a)) ∷
    ("usefulness" , axis (L.Assessment.usefulness a)) ∷ ("rationale" , V.string (L.Assessment.rationale a)) ∷
    ("evidence_indices" , V.array (map V.unsigned (L.Assessment.evidenceIndices a))) ∷
    ("item_ids" , V.array (map uuid (L.Assessment.itemIDs a))) ∷ [])

  experience : X.Experience → V.Value
  experience x = object (("id" , uuid (X.Experience.identity x)) ∷ ("project" , V.string (X.Experience.project x)) ∷
    ("context" , V.string (X.Experience.context x)) ∷ ("action" , V.string (X.Experience.action x)) ∷
    ("outcome" , V.string (outcomeText (X.Experience.outcome x))) ∷
    ("source" , V.string (Source.provenanceText (X.Experience.provenance x))) ∷
    ("evidence" , V.array (map V.string (X.Experience.evidence x))) ∷
    ("belief_ids" , V.array (map uuid (X.Experience.beliefIDs x))) ∷
    ("pattern_id" , optional uuid (X.Experience.patternID x)) ∷
    (nonempty "learning_items" item (X.Experience.items x) ++ nonempty "source_records" Source.encode (X.Experience.sources x)))

  feedback : R.Feedback → V.Value
  feedback f = object (("belief_id" , uuid (R.Feedback.beliefID f)) ∷
    ("verdict" , V.string (verdictText (R.Feedback.verdict f))) ∷ ("weight" , V.floating (R.Feedback.weight f)) ∷ [])

  link : R.Link → V.Value
  link l = object (("from_id" , uuid (R.Link.from l)) ∷ ("to_id" , uuid (R.Link.to l)) ∷
    ("relation" , V.string (relationText (R.Link.relation l))) ∷ ("weight" , V.floating (R.Link.weight l)) ∷ [])

  candidateFeedback : R.CandidateFeedback → V.Value
  candidateFeedback f = object (("target" , target (R.CandidateFeedback.target f)) ∷
    ("verdict" , V.string (verdictText (R.CandidateFeedback.verdict f))) ∷
    ("weight" , V.floating (R.CandidateFeedback.weight f)) ∷ [])

  candidateLink : R.CandidateLink → V.Value
  candidateLink l = object (("from" , target (R.CandidateLink.from l)) ∷ ("to" , target (R.CandidateLink.to l)) ∷
    ("relation" , V.string (relationText (R.CandidateLink.relation l))) ∷ ("weight" , V.floating (R.CandidateLink.weight l)) ∷ [])

  coverage : Coverage.Coverage → V.Value
  coverage c = object (("source_ref" , V.string (Coverage.Coverage.reference c)) ∷
    ("status" , V.string (coverageText (Coverage.Coverage.status c))) ∷ ("reason" , V.string (Coverage.Coverage.reason c)) ∷ [])

  candidate : Declaration.Candidate → V.Value
  candidate (Declaration.belief key content memory source) = object
    (("kind" , V.string (toList "belief")) ∷ ("key" , V.string key) ∷ ("content" , V.string content) ∷
      ("memory_type" , V.string (Candidate.memoryText memory)) ∷ presentField "supporting_passage_id" uuid source)
  candidate (Declaration.patternCandidate key situation approach) = object
    (("kind" , V.string (toList "pattern")) ∷ ("key" , V.string key) ∷
      ("situation" , V.string situation) ∷ ("approach" , V.string approach) ∷ [])

  review : R.Review → V.Value
  review r = object (("experience_id" , uuid (R.Review.experienceID r)) ∷
    ("experience_revision" , V.signed (R.Review.experienceRevision r)) ∷ ("reviewer" , V.string (R.Review.reviewer r)) ∷
    ("rationale" , V.string (R.Review.rationale r)) ∷ ("feedback" , V.array (map feedback (R.Review.feedbacks r))) ∷
    ("links" , V.array (map link (R.Review.links r))) ∷ ("superseded_beliefs" , V.array (map uuid (R.Review.superseded r))) ∷
    ("candidates" , V.array (map candidate (R.Review.candidates r))) ∷
    ("candidate_feedback" , V.array (map candidateFeedback (R.Review.candidateFeedbacks r))) ∷
    ("candidate_links" , V.array (map candidateLink (R.Review.candidateLinks r))) ∷
    (nonempty "assessments" assessment (R.Review.assessments r) ++ nonempty "extracted_items" item (R.Review.extracted r) ++
      nonempty "source_coverage" coverage (R.Review.coverage r)))

  snapshot : Observation.Snapshot → V.Value
  snapshot s = object (("experience" , experience (Observation.Snapshot.experience s)) ∷
    ("revision" , V.signed (Observation.Snapshot.revision s)) ∷ ("review_revision" , V.signed (Observation.Snapshot.reviewRevision s)) ∷
    ("reviewed_revision" , V.signed (Observation.Snapshot.reviewedRevision s)) ∷ candidates (Observation.Snapshot.candidateIDs s))
    where
    candidates : List (Text × UUID) → List (String × V.Value)
    candidates [] = []
    candidates pairs@(_ ∷ _) = ("candidate_ids" , V.object (map (λ { (key , id) → key , uuid id }) pairs)) ∷ []

  reference : Evidence.Reference → V.Value
  reference r = object (("chunk_id" , uuid (Evidence.Reference.chunk r)) ∷
    ("document_path" , V.string (Evidence.Reference.document r)) ∷ ("section_path" , V.array (map V.string (Evidence.Reference.section r))) ∷
    ("snippet" , V.string (Evidence.Reference.snippet r)) ∷ ("weight" , real (Evidence.Reference.weight r)) ∷ [])

  grounded : Evidence.Grounded → V.Value
  grounded b with belief (Evidence.Grounded.belief b)
  ... | V.object fields = V.object ((toList "evidence" , V.array (map reference (Evidence.Grounded.evidence b))) ∷ fields)
  ... | other = other

  documentHit : Document.Hit → V.Value
  documentHit h = object (("id" , uuid (Document.Hit.identity h)) ∷ ("document_path" , V.string (Document.Hit.document h)) ∷
    ("section_path" , V.array (map V.string (Document.Hit.section h))) ∷ ("content" , V.string (Document.Hit.content h)) ∷
    parentField (Document.Hit.parentContent h))
    where
    parentField : Maybe Text → List (String × V.Value)
    parentField nothing = []
    parentField (just text) = ("parent_content" , V.string text) ∷ []

  scores : Scores.Scores → V.Value
  scores s = object (("model_version" , V.unsigned (Scores.Scores.modelVersion s)) ∷
    ("correctness" , real (Scores.Scores.correctness s)) ∷ ("usefulness" , real (Scores.Scores.usefulness s)) ∷
    ("alpha" , real (Scores.Scores.alpha s)) ∷ ("beta" , real (Scores.Scores.beta s)) ∷
    ("benefit_sum" , real (Scores.Scores.benefitSum s)) ∷ ("correctness_mass" , real (Scores.Scores.correctnessMass s)) ∷
    ("usefulness_mass" , real (Scores.Scores.usefulnessMass s)) ∷ ("correctness_spread" , real (Scores.Scores.correctnessSpread s)) ∷
    ("incidents" , V.signed (Scores.Scores.incidents s)) ∷ ("unresolved_correctness" , V.signed (Scores.Scores.unresolvedCorrectness s)) ∷
    ("unresolved_usefulness" , V.signed (Scores.Scores.unresolvedUsefulness s)) ∷ ("calibrated" , V.boolean (Scores.Scores.calibrated s)) ∷ [])

  assessmentEntry : Assessment.Entry → V.Value
  assessmentEntry e = object (("experience_id" , uuid (Contributions.Row.experience c)) ∷
    ("review_revision" , V.unsigned (Contributions.Row.revision c)) ∷ ("experience_revision" , V.unsigned (Assessment.Entry.experienceRevision e)) ∷
    ("assessment" , assessment (Contributions.Row.payload c)) ∷ ("created_at" , optional timestamp (Assessment.Entry.timestamp e)) ∷
    ("active" , V.boolean (Assessment.Entry.active e)) ∷ [])
    where c = Assessment.Entry.contribution e

  historyEntry : ∀ {A : Set} → (A → V.Value) → History.Entry A → V.Value
  historyEntry encode e = object (("revision" , V.unsigned (History.Entry.revision e)) ∷
    ("payload" , encode (History.Entry.payload e)) ∷ ("created_at" , timestamp (History.Entry.createdAt e)) ∷ [])
