{-# OPTIONS --safe #-}
-- Public tools decode only after their supplied argument fields are known.
-- Nested typed records retain their strict field rules.
module Mimir.PublicRequest where

open import Data.Bool using (Bool; true; false)
open import Data.Float.Base using (Float; _*_)
open import Data.Integer using (ℤ; +_) renaming (_*_ to _*ℤ_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; s≤s; z≤n)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String; toList)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.Validation using (Fault)
open import Mimir.RecordDecoding using (_>>=_; mapResult; readArray)
open import Mimir.PublicInput
import Mimir.StructuredValue as V
import Mimir.Binary64 as Binary
import Mimir.ApplicationFloat as Numeric
import Mimir.StandardLibrary as Conversion
import Mimir.ToolCatalog as Tools
import Mimir.RetrievalRanking as Ranking
import Mimir.GraphMutationProtocol as Mutation
import Mimir.GraphNumerics as Numerics
import Mimir.GraphReadProtocol as Read
import Mimir.GraphDeletion as Delete
import Mimir.InferenceProtocol as Inference
import Mimir.LearningOperations as Learning
import Mimir.LearningQueryProtocol as Query
import Mimir.LearningWire as Wire
import Mimir.LearningCandidates as C
import Mimir.ReviewSchema as R
import Mimir.AssessmentSelection as Assessment
import Mimir.IndependentProvenance as Origin
import Mimir.Validation as Validation
open import Mimir.JsonObjects using (forbid)

data Request : Set where
  mutation : Mutation.Request → Request
  read : Read.Request → Request
  delete : Delete.Kind → ℕ → Request
  deleteProject : Text → Request
  inference : Inference.Request → Request
  sweepConfigured : Maybe Text → Float → Request
  relevant : Text → Ranking.Selection → Maybe Text → Maybe C.Memory → Bool → Ranking.Selection → Request
  addEvidence : ℕ → ℕ → Float → Request -- belief, chunk, weight
  removeEvidence : ℕ → ℕ → Request -- existing core-library API; no new MCP tool
  evidence : ℕ → Request
  loadDocument : Text → Maybe Text → Request
  queryDocument : Text → Maybe Text → Ranking.Selection → Request
  clearDocument : Text → Request
  learning : Learning.Request → Request
  learningQuery : Query.Request → Request
  learningContext : Text → Text → Ranking.Selection → Request
  capabilities : Request

memory : V.Value → Fault ⊎ C.Memory
memory = enum (("fact" , C.fact) ∷ ("experiential" , C.experiential) ∷ ("working" , C.working) ∷ [])

-- A missing or non-string memory field is absent; a string with an unknown
-- spelling is an error. This differs from the nested candidate enum grammar.
memoryField : Text → V.Object.View → Fault ⊎ Maybe C.Memory
memoryField name fields with fields name
... | just (V.string text) = mapResult just (memory (V.string text))
... | _ = inj₂ nothing

defaultMemory : Maybe C.Memory → C.Memory
defaultMemory nothing = C.fact
defaultMemory (just kind) = kind

-- Closed argument-field inventory. A new tool requires an explicit clause.
acceptedFields : Tools.Tool → List Text
acceptedFields Tools.insertBelief = Data.List.map toList ("confidence" ∷ "content" ∷ "memory_type" ∷ "probability" ∷ "project" ∷ "provenance" ∷ [])
acceptedFields Tools.deleteBelief = Data.List.map toList ("id" ∷ [])
acceptedFields Tools.deleteProject = Data.List.map toList ("project" ∷ [])
acceptedFields Tools.deletePattern = Data.List.map toList ("id" ∷ [])
acceptedFields Tools.insertPattern = Data.List.map toList ("approach" ∷ "project" ∷ "situation" ∷ "success_rate" ∷ [])
acceptedFields Tools.recordSupport = Data.List.map toList ("from_id" ∷ "to_id" ∷ "weight" ∷ [])
acceptedFields Tools.recordCause = Data.List.map toList ("from_id" ∷ "to_id" ∷ "weight" ∷ [])
acceptedFields Tools.recordDefeat = Data.List.map toList ("from_id" ∷ "to_id" ∷ "weight" ∷ [])
acceptedFields Tools.recordContradiction = Data.List.map toList ("id_a" ∷ "id_b" ∷ "weight" ∷ [])
acceptedFields Tools.getBelief = Data.List.map toList ("id" ∷ [])
acceptedFields Tools.listBeliefs = Data.List.map toList ("limit" ∷ "memory_type" ∷ "offset" ∷ "project" ∷ [])
acceptedFields Tools.listPatterns = Data.List.map toList ("project" ∷ [])
acceptedFields Tools.getContradictions = Data.List.map toList ("project" ∷ [])
acceptedFields Tools.decayAll = Data.List.map toList ("decay_factor" ∷ "project" ∷ [])
acceptedFields Tools.sweepExpiredDefeated = Data.List.map toList ("prob_threshold" ∷ "project" ∷ [])
acceptedFields Tools.queryRelevant = Data.List.map toList ("context" ∷ "evidence_per_belief" ∷ "include_evidence" ∷ "limit" ∷ "prefer_type" ∷ "project" ∷ [])
acceptedFields Tools.addEvidence = Data.List.map toList ("belief_id" ∷ "chunk_id" ∷ "weight" ∷ [])
acceptedFields Tools.getEvidence = Data.List.map toList ("belief_id" ∷ [])
acceptedFields Tools.propagateFrom = Data.List.map toList ("id" ∷ [])
acceptedFields Tools.queryIntervention = Data.List.map toList ("id" ∷ "value" ∷ [])
acceptedFields Tools.loadDocument = Data.List.map toList ("path" ∷ "project" ∷ [])
acceptedFields Tools.queryDocument = Data.List.map toList ("context" ∷ "limit" ∷ "project" ∷ [])
acceptedFields Tools.clearDocument = Data.List.map toList ("path" ∷ [])
acceptedFields Tools.getLearningReview = Data.List.map toList ("id" ∷ [])
acceptedFields Tools.learningCapabilities = []
acceptedFields Tools.getLessonAssessment = Data.List.map toList ("belief_id" ∷ "project" ∷ "rubric" ∷ "scope" ∷ [])
acceptedFields Tools.lessonAssessmentHistory = Data.List.map toList ("belief_id" ∷ "limit" ∷ "offset" ∷ "project" ∷ "rubric" ∷ "scope" ∷ [])
acceptedFields Tools.explainBelief = Data.List.map toList ("id" ∷ "limit" ∷ "offset" ∷ [])
acceptedFields Tools.recordExperience = Data.List.map toList ("expected_revision" ∷ "experience" ∷ [])
acceptedFields Tools.pendingExperiences = Data.List.map toList ("exclude_ids" ∷ "limit" ∷ "project" ∷ [])
acceptedFields Tools.reviewExperience = Data.List.map toList ("expected_review_revision" ∷ "review" ∷ [])
acceptedFields Tools.getExperience = Data.List.map toList ("id" ∷ [])
acceptedFields Tools.experienceHistory = Data.List.map toList ("id" ∷ [])
acceptedFields Tools.queryLearningContext = Data.List.map toList ("context" ∷ "limit" ∷ "project" ∷ [])

module Decode (conversion : Conversion.Contract) where
  open Numbers conversion
  sizeMaximum = Binary.powerMinusOne 64 -- installed 64-bit target
  module L = Wire.Decode conversion sizeMaximum

  float : V.Value → Fault ⊎ Float
  float raw = number raw >>= λ n → fromNumber n
    where
    fromNumber : Binary.Number → Fault ⊎ Float
    fromNumber n with Numeric.number n
    ... | nothing = bad "nonfinite JSON number"
    ... | just value = inj₂ value

  unitProbability : V.Value → Fault ⊎ Float
  unitProbability raw = float raw >>= checked
    where
    checked : Float → Fault ⊎ Float
    checked value with Numerics.probability value
    ... | true = inj₂ value
    ... | false = inj₁ (Validation.fault [] Validation.invalidNumber
      "Supply a finite probability between 0 and 1 inclusive; do not clamp or guess a replacement")

  project : V.Object.View → Maybe Text
  project = looseOptional "project" V.asString

  integer : V.Value → Fault ⊎ ℕ
  integer = unsigned sizeMaximum

  assessmentQuery : V.Object.View → Fault ⊎ Assessment.Query
  assessmentQuery fields = required "project" V.asString fields >>= λ project →
    required "belief_id" uuid fields >>= λ id → required "scope" V.asString fields >>= λ scope →
    required "rubric" V.asString fields >>= λ rubric → inj₂ (Assessment.query project id scope rubric)

  selectedCount : V.Value → Fault ⊎ Ranking.PositiveCount
  selectedCount raw = integer raw >>= λ
    { zero → inj₁ (Validation.fault [] Validation.invalidNumber "selection must be positive; omit the field to return all matches")
    ; (suc n) → inj₂ (Ranking.positiveCount (suc n) (s≤s z≤n)) }

  selection : String → V.Object.View → Fault ⊎ Ranking.Selection
  selection fieldName fields = present fieldName selectedCount fields

  listRequest : V.Object.View → Maybe C.Memory → Fault ⊎ Request
  listRequest fields memory with fields (toList "limit")
  ... | nothing with fields (toList "offset")
  ...   | nothing = inj₂ (read (Read.listBeliefs (project fields) memory))
  ...   | just _ = bad "offset requires limit"
  listRequest fields memory | just raw = required "limit" selectedCount fields >>= λ selected →
    defaulted "offset" 0 integer fields >>= λ offset →
    inj₂ (read (Read.beliefPage (project fields) memory (Ranking.PositiveCount.count selected) offset))

  edgeRequest : R.Relation → V.Object.View → Fault ⊎ Request
  edgeRequest relation fields = required "from_id" V.asString fields >>= λ fromText →
    required "to_id" V.asString fields >>= λ toText → required "weight" number fields >>= λ weight →
    uuid (V.string fromText) >>= λ from → uuid (V.string toText) >>= λ to →
    inj₂ (mutation (Mutation.edge from to relation weight))

  validOrigin : V.Value → Fault ⊎ Origin.Provenance
  validOrigin raw = Wire.origin raw >>= check
    where
    check : Origin.Provenance → Fault ⊎ Origin.Provenance
    check origin with Origin.validate origin
    ... | Validation.rejected fault invalid = inj₁ fault
    ... | Validation.accepted valid = inj₂ origin

  decode : Tools.Tool → V.Object.View → Fault ⊎ Request
  decode Tools.insertBelief fields = required "provenance" validOrigin fields >>= λ origin →
    required "content" V.asString fields >>= λ content → required "probability" unitProbability fields >>= λ probability →
    required "confidence" unitProbability fields >>= λ confidence → memoryField (toList "memory_type") fields >>= λ kind →
    inj₂ (mutation (Mutation.belief content probability confidence (project fields) (defaultMemory kind) (just origin)))
  decode Tools.deleteBelief fields = mapResult (delete Delete.belief) (required "id" uuid fields)
  decode Tools.deletePattern fields = mapResult (delete Delete.patternNode) (required "id" uuid fields)
  decode Tools.deleteProject fields = mapResult deleteProject (required "project" V.asString fields)
  decode Tools.insertPattern fields = required "situation" V.asString fields >>= λ situation →
    required "approach" V.asString fields >>= λ approach → required "success_rate" unitProbability fields >>= λ success →
    present "project" V.asString fields >>= λ project → inj₂ (mutation (Mutation.patternNode situation approach success project))
  decode Tools.recordSupport fields = edgeRequest R.supports fields
  decode Tools.recordCause fields = edgeRequest R.causes fields
  decode Tools.recordDefeat fields = edgeRequest R.defeats fields
  decode Tools.recordContradiction fields = required "id_a" V.asString fields >>= λ fromText →
    required "id_b" V.asString fields >>= λ toText → castNatural 1 >>= λ one →
    uuid (V.string fromText) >>= λ from → uuid (V.string toText) >>= λ to →
    inj₂ (mutation (Mutation.edge from to R.contradicts (loose "weight" one number fields)))
  decode Tools.getBelief fields = mapResult (λ id → read (Read.getBelief id)) (required "id" uuid fields)
  decode Tools.listBeliefs fields = memoryField (toList "memory_type") fields >>= listRequest fields
  decode Tools.listPatterns fields = inj₂ (read (Read.listPatterns (project fields)))
  decode Tools.getContradictions fields = inj₂ (inference (Inference.contradictions (project fields)))
  decode Tools.decayAll fields = inj₂ (inference (Inference.decay (project fields) (loose "decay_factor" 0.99 float fields)))
  decode Tools.sweepExpiredDefeated fields = defaulted "prob_threshold" 0.3 unitProbability fields >>= λ threshold →
    inj₂ (sweepConfigured (project fields) threshold)
  decode Tools.queryRelevant fields = required "context" V.asString fields >>= λ context →
    memoryField (toList "prefer_type") fields >>= λ preference →
    selection "limit" fields >>= λ limit → selection "evidence_per_belief" fields >>= λ per →
    inj₂ (relevant context limit (project fields) preference
      (loose "include_evidence" false V.asBoolean fields) per)
  decode Tools.addEvidence fields = required "belief_id" V.asString fields >>= λ beliefText →
    required "chunk_id" V.asString fields >>= λ chunkText →
    uuid (V.string beliefText) >>= λ belief → uuid (V.string chunkText) >>= λ chunk →
    inj₂ (addEvidence belief chunk (loose "weight" 1.0 float fields))
  decode Tools.getEvidence fields = mapResult evidence (required "belief_id" uuid fields)
  decode Tools.propagateFrom fields = mapResult (λ id → inference (Inference.propagate id)) (required "id" uuid fields)
  decode Tools.queryIntervention fields = required "id" V.asString fields >>= λ text → required "value" float fields >>= λ value →
    uuid (V.string text) >>= λ id → inj₂ (inference (Inference.intervention id value))
  decode Tools.loadDocument fields = required "path" V.asString fields >>= λ path → inj₂ (loadDocument path (project fields))
  decode Tools.queryDocument fields = required "context" V.asString fields >>= λ context →
    selection "limit" fields >>= λ limit → inj₂ (queryDocument context (project fields) limit)
  decode Tools.clearDocument fields = mapResult clearDocument (required "path" V.asString fields)
  decode Tools.getLearningReview fields = mapResult (λ id → learningQuery (Query.currentReview id)) (required "id" uuid fields)
  decode Tools.learningCapabilities fields = inj₂ capabilities
  decode Tools.getLessonAssessment fields = mapResult (λ q → learningQuery (Query.score q)) (assessmentQuery fields)
  decode Tools.lessonAssessmentHistory fields = assessmentQuery fields >>= λ q →
    defaulted "offset" 0 integer fields >>= λ offset → defaulted "limit" 20 integer fields >>= λ limit →
    inj₂ (learningQuery (Query.assessmentHistory q offset limit))
  decode Tools.explainBelief fields = required "id" uuid fields >>= λ id →
    defaulted "offset" 0 integer fields >>= λ offset → defaulted "limit" 10 integer fields >>= λ limit →
    inj₂ (read (Read.explain id offset limit))
  decode Tools.recordExperience fields = required "experience" L.experienceInput fields >>= λ experience →
    required "expected_revision" i64 fields >>= λ expected → inj₂ (learning (Learning.recordExperience experience expected))
  decode Tools.reviewExperience fields = required "review" L.reviewInput fields >>= λ review →
    required "expected_review_revision" i64 fields >>= λ expected → inj₂ (learning (Learning.reviewExperience review expected))
  decode Tools.pendingExperiences fields = present "project" V.asString fields >>= λ project →
    selection "limit" fields >>= λ limit → defaulted "exclude_ids" [] (readArray uuid) fields >>= λ excluded →
    inj₂ (learningQuery (Query.pending project (Data.Maybe.map Ranking.PositiveCount.count limit) excluded))
  decode Tools.getExperience fields = mapResult (λ id → learningQuery (Query.experience id)) (required "id" uuid fields)
  decode Tools.experienceHistory fields = mapResult (λ id → learningQuery (Query.history id)) (required "id" uuid fields)
  decode Tools.queryLearningContext fields = required "context" V.asString fields >>= λ context →
    required "project" V.asString fields >>= λ project → selection "limit" fields >>= λ limit →
    inj₂ (learningContext context project limit)

  -- A supplied optional value must pass its decoder before any loose
  -- legacy accessor can select a fallback. Omission retains the advertised
  -- behavior; wrong types never become omission.
  supplied : ∀ {A : Set} → String → (V.Value → Fault ⊎ A) → V.Object.View → Fault ⊎ ⊤
  supplied name decoder fields = present name decoder fields >>= λ _ → inj₂ tt

  suppliedTypes : V.Object.View → Fault ⊎ ⊤
  suppliedTypes fields = supplied "project" V.asString fields >>= λ _ →
    supplied "memory_type" V.asString fields >>= λ _ →
    supplied "prefer_type" V.asString fields >>= λ _ →
    supplied "limit" integer fields >>= λ _ →
    supplied "offset" integer fields >>= λ _ →
    supplied "evidence_per_belief" integer fields >>= λ _ →
    supplied "include_evidence" V.asBoolean fields >>= λ _ →
    supplied "decay_factor" unitProbability fields >>= λ _ →
    supplied "prob_threshold" unitProbability fields >>= λ _ →
    supplied "weight" unitProbability fields >>= λ _ →
    supplied "value" unitProbability fields

  admittedFields : Tools.Tool → V.Object.View → Fault ⊎ Request
  admittedFields tool fields = suppliedTypes fields >>= λ _ → decode tool fields

  readTool : Tools.Tool → V.Value → Fault ⊎ Request
  readTool tool (V.object fields) with V.Object.checkUnknowns forbid (acceptedFields tool) fields
  ... | Validation.rejected detail invalid = inj₁ detail
  ... | Validation.accepted known = admittedFields tool (V.Object.normalize fields)
  readTool tool _ = inj₁ (Validation.fault [] Validation.wrongType "Tool arguments must be an object")

  successfulRequestHasKnownFields : ∀ tool fields requestValue →
    readTool tool (V.object fields) ≡ inj₂ requestValue →
    V.Object.UnknownsAllowed forbid (acceptedFields tool) fields
  successfulRequestHasKnownFields tool fields requestValue proof
    with V.Object.checkUnknowns forbid (acceptedFields tool) fields
  ... | Validation.rejected detail invalid with proof
  ...   | ()
  successfulRequestHasKnownFields tool fields requestValue proof | Validation.accepted known = known

  invalidSuppliedValuePreventsExecution : ∀ tool fields detail →
    suppliedTypes fields ≡ inj₁ detail → admittedFields tool fields ≡ inj₁ detail
  invalidSuppliedValuePreventsExecution tool fields detail rejected rewrite rejected = refl
