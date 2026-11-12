{-# OPTIONS --safe #-}
-- All 34 MCP tools decode to concrete application operations. Invalid or
-- unknown fields are reported to the caller for correction.
module Mimir.PublicRequest where

open import Data.Bool using (Bool; true; false)
open import Data.Float.Base using (Float; _*_)
open import Data.Integer using (ℤ; +_) renaming (_*_ to _*ℤ_)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (toList)
open import Relation.Nullary using (yes; no)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.UUIDGroups using (UUID)
open import Mimir.Validation using (Fault)
open import Mimir.RecordDecoding using (_>>=_; mapResult; readArray)
open import Mimir.PublicInput
import Mimir.StructuredValue as V
import Mimir.Binary64 as Binary
import Mimir.ApplicationFloat as Numeric
import Mimir.StandardLibrary as Conversion
import Mimir.ToolCatalog as Tools
import Mimir.GraphMutationProtocol as Mutation
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
open import Mimir.Collections using (module Equality)

module FieldNames = Equality Text _≟Text_

duplicateField : List (Text × V.Value) → Maybe Text
duplicateField [] = nothing
duplicateField ((name , value) ∷ rest) with FieldNames.present? name (map proj₁ rest)
... | yes repeated = just name
... | no unique = duplicateField rest

data Request : Set where
  mutation : Mutation.Request → Request
  read : Read.Request → Request
  delete : Delete.Kind → UUID → Request
  deleteProject : Text → Request
  inference : Inference.Request → Request
  sweepConfigured : Maybe Text → Float → Request
  relevant : Text → Maybe ℕ → Maybe Text → Maybe C.Memory → Bool → Maybe ℕ → Request
  addEvidence : UUID → UUID → Float → Request -- belief, chunk, weight
  removeEvidence : UUID → UUID → Request -- existing core-library API; no new MCP tool
  evidence : UUID → Request
  loadDocument : Text → Maybe Text → Request
  queryDocument : Text → Maybe Text → Maybe ℕ → Request
  clearDocument : Text → Request
  learning : Learning.Request → Request
  learningQuery : Query.Request → Request
  learningContext : Text → Text → Maybe ℕ → Request
  capabilities : Request

memory : V.Value → Fault ⊎ C.Memory
memory = enum (("fact" , C.fact) ∷ ("experiential" , C.experiential) ∷ ("working" , C.working) ∷ [])

-- The same public tool name selects both its accepted fields and decoder.
allowedFields : Tools.Tool → List Text
allowedFields Tools.insertBelief = map toList ("provenance" ∷ "content" ∷ "probability" ∷ "confidence" ∷ "memory_type" ∷ "project" ∷ [])
allowedFields Tools.deleteBelief = map toList ("id" ∷ [])
allowedFields Tools.deleteProject = map toList ("project" ∷ [])
allowedFields Tools.deletePattern = map toList ("id" ∷ [])
allowedFields Tools.insertPattern = map toList ("situation" ∷ "approach" ∷ "success_rate" ∷ "project" ∷ [])
allowedFields Tools.recordSupport = map toList ("from_id" ∷ "to_id" ∷ "weight" ∷ [])
allowedFields Tools.recordCause = map toList ("from_id" ∷ "to_id" ∷ "weight" ∷ [])
allowedFields Tools.recordDefeat = map toList ("from_id" ∷ "to_id" ∷ "weight" ∷ [])
allowedFields Tools.recordContradiction = map toList ("id_a" ∷ "id_b" ∷ "weight" ∷ [])
allowedFields Tools.getBelief = map toList ("id" ∷ [])
allowedFields Tools.listBeliefs = map toList ("project" ∷ "memory_type" ∷ "limit" ∷ "offset" ∷ [])
allowedFields Tools.listPatterns = map toList ("project" ∷ [])
allowedFields Tools.getContradictions = map toList ("project" ∷ [])
allowedFields Tools.decayAll = map toList ("project" ∷ "decay_factor" ∷ [])
allowedFields Tools.sweepExpiredDefeated = map toList ("project" ∷ "prob_threshold" ∷ [])
allowedFields Tools.queryRelevant = map toList ("context" ∷ "limit" ∷ "project" ∷ "prefer_type" ∷ "include_evidence" ∷ "evidence_per_belief" ∷ [])
allowedFields Tools.addEvidence = map toList ("belief_id" ∷ "chunk_id" ∷ "weight" ∷ [])
allowedFields Tools.getEvidence = map toList ("belief_id" ∷ [])
allowedFields Tools.propagateFrom = map toList ("id" ∷ [])
allowedFields Tools.queryIntervention = map toList ("id" ∷ "value" ∷ [])
allowedFields Tools.loadDocument = map toList ("path" ∷ "project" ∷ [])
allowedFields Tools.queryDocument = map toList ("context" ∷ "project" ∷ "limit" ∷ [])
allowedFields Tools.clearDocument = map toList ("path" ∷ [])
allowedFields Tools.getLearningReview = map toList ("id" ∷ [])
allowedFields Tools.learningCapabilities = []
allowedFields Tools.getLessonAssessment = map toList ("project" ∷ "belief_id" ∷ "scope" ∷ "rubric" ∷ [])
allowedFields Tools.lessonAssessmentHistory = map toList ("project" ∷ "belief_id" ∷ "scope" ∷ "rubric" ∷ "offset" ∷ "limit" ∷ [])
allowedFields Tools.explainBelief = map toList ("id" ∷ "offset" ∷ "limit" ∷ [])
allowedFields Tools.recordExperience = map toList ("experience" ∷ "expected_revision" ∷ [])
allowedFields Tools.pendingExperiences = map toList ("project" ∷ "limit" ∷ "exclude_ids" ∷ [])
allowedFields Tools.reviewExperience = map toList ("review" ∷ "expected_review_revision" ∷ [])
allowedFields Tools.getExperience = map toList ("id" ∷ [])
allowedFields Tools.experienceHistory = map toList ("id" ∷ [])
allowedFields Tools.queryLearningContext = map toList ("context" ∷ "project" ∷ "limit" ∷ [])

-- An omitted preference is absent; an invalid supplied value is correctable.
memoryField : Text → V.Object.View → Fault ⊎ Maybe C.Memory
memoryField name fields with fields name
... | nothing = inj₂ nothing
... | just raw = mapResult just (V.withField name (memory raw))

defaultMemory : Maybe C.Memory → C.Memory
defaultMemory nothing = C.fact
defaultMemory (just kind) = kind

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

  project : V.Object.View → Fault ⊎ Maybe Text
  project = present "project" V.asString

  integer : V.Value → Fault ⊎ ℕ
  integer = unsigned sizeMaximum

  positive : V.Value → Fault ⊎ ℕ
  positive raw = integer raw >>= λ where
    zero → inj₁ (Validation.fault [] Validation.invalidNumber "limit must be greater than zero")
    (suc n) → inj₂ (suc n)

  assessmentQuery : V.Object.View → Fault ⊎ Assessment.Query
  assessmentQuery fields = required "project" V.asString fields >>= λ project →
    required "belief_id" uuid fields >>= λ id → required "scope" V.asString fields >>= λ scope →
    required "rubric" V.asString fields >>= λ rubric → inj₂ (Assessment.query project id scope rubric)

  listRequestWith : Maybe Text → V.Object.View → Maybe C.Memory → Fault ⊎ Request
  listRequestWith selectedProject fields memory with fields (toList "limit")
  ... | nothing with fields (toList "offset")
  ...   | nothing = inj₂ (read (Read.listBeliefs selectedProject memory))
  ...   | just _ = inj₁ (Validation.fault (Validation.fieldKey (toList "offset") ∷ []) Validation.malformedInput "offset requires limit")
  listRequestWith selectedProject fields memory | just raw = V.withField (toList "limit") (positive raw) >>= λ limit →
    defaulted "offset" 0 integer fields >>= λ offset →
    inj₂ (read (Read.beliefPage selectedProject memory limit offset))

  listRequest : V.Object.View → Maybe C.Memory → Fault ⊎ Request
  listRequest fields memory = project fields >>= λ selectedProject → listRequestWith selectedProject fields memory

  edgeRequest : R.Relation → V.Object.View → Fault ⊎ Request
  edgeRequest relation fields = required "from_id" uuid fields >>= λ from →
    required "to_id" uuid fields >>= λ to → required "weight" number fields >>= λ weight →
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
    required "content" V.asString fields >>= λ content → required "probability" float fields >>= λ probability →
    required "confidence" float fields >>= λ confidence → memoryField (toList "memory_type") fields >>= λ kind →
    project fields >>= λ selectedProject →
    inj₂ (mutation (Mutation.belief content probability confidence selectedProject (defaultMemory kind) (just origin)))
  decode Tools.deleteBelief fields = mapResult (delete Delete.belief) (required "id" uuid fields)
  decode Tools.deletePattern fields = mapResult (delete Delete.patternNode) (required "id" uuid fields)
  decode Tools.deleteProject fields = mapResult deleteProject (required "project" V.asString fields)
  decode Tools.insertPattern fields = required "situation" V.asString fields >>= λ situation →
    required "approach" V.asString fields >>= λ approach → required "success_rate" float fields >>= λ success →
    present "project" V.asString fields >>= λ project → inj₂ (mutation (Mutation.patternNode situation approach success project))
  decode Tools.recordSupport fields = edgeRequest R.supports fields
  decode Tools.recordCause fields = edgeRequest R.causes fields
  decode Tools.recordDefeat fields = edgeRequest R.defeats fields
  decode Tools.recordContradiction fields = required "id_a" uuid fields >>= λ from →
    required "id_b" uuid fields >>= λ to → castNatural 1 >>= λ one →
    defaulted "weight" one number fields >>= λ weight →
    inj₂ (mutation (Mutation.edge from to R.contradicts weight))
  decode Tools.getBelief fields = mapResult (λ id → read (Read.getBelief id)) (required "id" uuid fields)
  decode Tools.listBeliefs fields = memoryField (toList "memory_type") fields >>= listRequest fields
  decode Tools.listPatterns fields = project fields >>= λ selectedProject → inj₂ (read (Read.listPatterns selectedProject))
  decode Tools.getContradictions fields = project fields >>= λ selectedProject → inj₂ (inference (Inference.contradictions selectedProject))
  decode Tools.decayAll fields = project fields >>= λ selectedProject →
    defaulted "decay_factor" 0.99 float fields >>= λ factor → inj₂ (inference (Inference.decay selectedProject factor))
  decode Tools.sweepExpiredDefeated fields = project fields >>= λ selectedProject →
    required "prob_threshold" float fields >>= λ threshold →
    inj₂ (sweepConfigured selectedProject threshold)
  decode Tools.queryRelevant fields = required "context" V.asString fields >>= λ context →
    memoryField (toList "prefer_type") fields >>= λ preference →
    project fields >>= λ selectedProject → optional "limit" positive fields >>= λ limit →
    defaulted "include_evidence" false V.asBoolean fields >>= λ include →
    optional "evidence_per_belief" positive fields >>= λ per →
    inj₂ (relevant context limit selectedProject preference include per)
  decode Tools.addEvidence fields = required "belief_id" uuid fields >>= λ belief →
    required "chunk_id" uuid fields >>= λ chunk →
    defaulted "weight" 1.0 float fields >>= λ weight → inj₂ (addEvidence belief chunk weight)
  decode Tools.getEvidence fields = mapResult evidence (required "belief_id" uuid fields)
  decode Tools.propagateFrom fields = mapResult (λ id → inference (Inference.propagate id)) (required "id" uuid fields)
  decode Tools.queryIntervention fields = required "id" uuid fields >>= λ id → required "value" float fields >>= λ value →
    inj₂ (inference (Inference.intervention id value))
  decode Tools.loadDocument fields = required "path" V.asString fields >>= λ path →
    project fields >>= λ selectedProject → inj₂ (loadDocument path selectedProject)
  decode Tools.queryDocument fields = required "context" V.asString fields >>= λ context →
    project fields >>= λ selectedProject → optional "limit" positive fields >>= λ limit →
    inj₂ (queryDocument context selectedProject limit)
  decode Tools.clearDocument fields = mapResult clearDocument (required "path" V.asString fields)
  decode Tools.getLearningReview fields = mapResult (λ id → learningQuery (Query.currentReview id)) (required "id" uuid fields)
  decode Tools.learningCapabilities fields = inj₂ capabilities
  decode Tools.getLessonAssessment fields = mapResult (λ q → learningQuery (Query.score q)) (assessmentQuery fields)
  decode Tools.lessonAssessmentHistory fields = assessmentQuery fields >>= λ q →
    defaulted "offset" 0 integer fields >>= λ offset → optional "limit" positive fields >>= λ limit →
    inj₂ (learningQuery (Query.assessmentHistory q offset limit))
  decode Tools.explainBelief fields = required "id" uuid fields >>= λ id →
    defaulted "offset" 0 integer fields >>= λ offset → optional "limit" positive fields >>= λ limit →
    inj₂ (read (Read.explain id offset limit))
  decode Tools.recordExperience fields = required "experience" L.experienceInput fields >>= λ experience →
    required "expected_revision" i64 fields >>= λ expected → inj₂ (learning (Learning.recordExperience experience expected))
  decode Tools.reviewExperience fields = required "review" L.reviewInput fields >>= λ review →
    required "expected_review_revision" i64 fields >>= λ expected → inj₂ (learning (Learning.reviewExperience review expected))
  decode Tools.pendingExperiences fields = present "project" V.asString fields >>= λ project →
    optional "limit" positive fields >>= λ limit → defaulted "exclude_ids" [] (readArray uuid) fields >>= λ excluded →
    inj₂ (learningQuery (Query.pending project limit excluded))
  decode Tools.getExperience fields = mapResult (λ id → learningQuery (Query.experience id)) (required "id" uuid fields)
  decode Tools.experienceHistory fields = mapResult (λ id → learningQuery (Query.history id)) (required "id" uuid fields)
  decode Tools.queryLearningContext fields = required "context" V.asString fields >>= λ context →
    required "project" V.asString fields >>= λ project → optional "limit" positive fields >>= λ limit →
    inj₂ (learningContext context project limit)

  readTool : Tools.Tool → V.Value → Fault ⊎ Request
  readTool tool (V.object fields) with duplicateField fields
  ... | just name = inj₁ (Validation.fault (Validation.fieldKey name ∷ []) Validation.duplicate "field is repeated")
  ... | nothing with Validation.result (V.Object.checkKnown (allowedFields tool) fields)
  ...   | inj₁ failure = inj₁ failure
  ...   | inj₂ known = decode tool (V.Object.normalize fields)
  readTool tool _ = bad "Tool arguments must be an object."
