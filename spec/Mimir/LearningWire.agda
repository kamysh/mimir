{-# OPTIONS --safe #-}
-- Complete typed learning request decoding, including nested records and
-- default/null/unknown-field distinctions. Stored responses require IDs;
-- public inputs retain optional IDs and keys until locked allocation. The
-- resulting canonical payload passes ExperienceSchema/ReviewSchema checks
-- inside the same operation before its proposed world is published.
module Mimir.LearningWire where

open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String; toList)
open import Mimir.Validation using (Fault)
open import Mimir.RecordDecoding using (_>>=_; mapResult; readRecord; readArray)
open import Mimir.PublicInput
import Mimir.StructuredValue as V
import Mimir.JsonObjects as Objects
import Mimir.StandardLibrary as Conversion
import Mimir.ExperienceSchema as X
import Mimir.ReviewSchema as R
import Mimir.LearningSchema as L
import Mimir.LearningCandidates as C
import Mimir.NumericValidation as N
import Mimir.SourceReview as Coverage
import Mimir.SourceWire as Source
import Mimir.CandidateWire as Candidate
import Mimir.IndependentProvenance as Origin
import Mimir.LearningInput as Input
import Mimir.SourceSchema as Sources
import Mimir.Validation as Validation

-- Allocation-independent source checks are shared by public admission and
-- saved-request readback. They retain the original unallocated input.
sourceHeader : Input.Experience → Fault ⊎ Input.Experience
sourceHeader value = mapResult (λ _ → value) (Validation.result
  (Validation.combine (Validation.at (Validation.key "learning_items") (Input.validateItems (Input.Experience.items value)))
  (Validation.combine (Sources.validateSources (Input.Experience.sources value))
    (Validation.combine (X.checkEvidenceReferences (Input.Experience.sources value) (Input.Experience.evidence value))
    (Validation.combine (Validation.at (Validation.key "project") (C.checkNonblank (Input.Experience.project value)))
    (Validation.combine (Validation.at (Validation.key "context") (C.checkNonblank (Input.Experience.context value)))
    (Validation.combine (Validation.at (Validation.key "action") (C.checkNonblank (Input.Experience.action value)))
      (X.checkOutcomeEvidence (Input.Experience.outcome value) (Input.Experience.evidence value)))))))))

reviewHeader : Input.Review → Fault ⊎ Input.Review
reviewHeader value = mapResult (λ _ → value) (Validation.result (Input.validateReview value))

recordOf : ∀ {A : Set} → List String → (V.Object.View → Fault ⊎ A) → V.Value → Fault ⊎ A
recordOf names = readRecord Objects.forbid Objects.keepLast (map toList names)

outcome : V.Value → Fault ⊎ X.Outcome
outcome = enum (("success" , X.success) ∷ ("failure" , X.failure) ∷ ("unknown" , X.unknown) ∷ [])

kind : V.Value → Fault ⊎ L.Kind
kind = enum (("estimate" , L.estimate) ∷ ("decision" , L.decision) ∷ ("suggestion" , L.suggestion) ∷ [])

verdict : V.Value → Fault ⊎ R.Verdict
verdict = enum (("support" , R.support) ∷ ("defeat" , R.defeat) ∷ [])

relation : V.Value → Fault ⊎ R.Relation
relation = enum (("Supports" , R.supports) ∷ ("Defeats" , R.defeats) ∷
  ("Causes" , R.causes) ∷ ("Contradicts" , R.contradicts) ∷ [])

coverage : V.Value → Fault ⊎ Coverage.Coverage
coverage = recordOf ("source_ref" ∷ "status" ∷ "reason" ∷ []) (λ fields →
  required "source_ref" V.asString fields >>= λ reference →
  required "status" (enum (("complete" , Coverage.complete) ∷ ("unresolved" , Coverage.unresolved) ∷ [])) fields >>= λ status →
  required "reason" V.asString fields >>= λ reason → inj₂ (Coverage.sourceCoverage reference status reason))

origin : V.Value → Fault ⊎ Origin.Provenance
origin = recordOf ("basis" ∷ "reference" ∷ []) (λ fields →
  required "basis" (enum (("user_instruction" , Origin.userInstruction) ∷ ("document" , Origin.document) ∷ [])) fields >>= λ basis →
  required "reference" V.asString fields >>= λ reference → inj₂ (Origin.provenance basis reference))

-- serde's untagged variants try Existing first, then Candidate. These two
-- variant records permit unrelated members; the enclosing records do not.
target : Conversion.Contract → V.Value → Fault ⊎ L.Target
target conversion raw with required "belief_id" (readUUID conversion) (view raw)
... | inj₂ id = inj₂ (L.existing id)
... | inj₁ first = mapResult L.candidate (required "candidate_key" V.asString (view raw))

module Decode (conversion : Conversion.Contract) (sizeMaximum : ℕ) where
  open Numbers conversion

  prediction : V.Value → Fault ⊎ L.Prediction
  prediction = recordOf ("quantity" ∷ "value" ∷ "unit" ∷ "probability" ∷ "lower" ∷ "upper" ∷
    "horizon" ∷ "recorded_at" ∷ "inferred" ∷ []) (λ fields →
    required "quantity" V.asString fields >>= λ quantity →
    required "value" number fields >>= λ value →
    required "unit" V.asString fields >>= λ unit →
    optional "probability" number fields >>= λ probability →
    optional "lower" number fields >>= λ lower →
    optional "upper" number fields >>= λ upper →
    required "horizon" V.asString fields >>= λ horizon →
    required "recorded_at" V.asString fields >>= λ recorded →
    required "inferred" V.asBoolean fields >>= λ inferred →
    inj₂ (L.prediction quantity unit horizon recorded value probability lower upper inferred))

  item : V.Value → Fault ⊎ L.LearningItem
  -- Stored responses require the assigned ID and retain the optional key.
  item = recordOf ("id" ∷ "key" ∷ "kind" ∷ "source_ref" ∷ "actor" ∷ "statement" ∷ "conditions" ∷ "predictions" ∷ [])
    (λ fields → required "id" uuid fields >>= λ id → optional "key" V.asString fields >>= λ localKey →
    required "kind" kind fields >>= λ kind →
    required "source_ref" V.asString fields >>= λ reference → required "actor" V.asString fields >>= λ actor →
    required "statement" V.asString fields >>= λ statement → required "conditions" V.asString fields >>= λ conditions →
    defaulted "predictions" [] (readArray prediction) fields >>= λ predictions →
    inj₂ (L.learningItem id localKey kind reference actor statement conditions predictions))

  itemInput : V.Value → Fault ⊎ Input.Item
  itemInput = recordOf ("id" ∷ "key" ∷ "kind" ∷ "source_ref" ∷ "actor" ∷ "statement" ∷ "conditions" ∷ "predictions" ∷ [])
    (λ fields → optional "id" uuid fields >>= λ id → optional "key" V.asString fields >>= λ localKey →
    required "kind" kind fields >>= λ kind →
    required "source_ref" V.asString fields >>= λ reference → required "actor" V.asString fields >>= λ actor →
    required "statement" V.asString fields >>= λ statement → required "conditions" V.asString fields >>= λ conditions →
    defaulted "predictions" [] (readArray prediction) fields >>= λ predictions →
    inj₂ (Input.item id localKey kind reference actor statement conditions predictions))

  axis : V.Value → Fault ⊎ N.Axis
  axis = recordOf ("value" ∷ "weight" ∷ []) (λ fields →
    optional "value" number fields >>= λ value → required "weight" number fields >>= λ weight → inj₂ (N.axis value weight))

  assessment : V.Value → Fault ⊎ L.Assessment
  -- ItemAllocation resolves item_keys to item_ids before this canonical read.
  assessment = recordOf ("target" ∷ "scope" ∷ "rubric" ∷ "correctness" ∷ "usefulness" ∷ "evidence_indices" ∷
    "item_ids" ∷ "rationale" ∷ []) (λ fields →
    required "target" (target conversion) fields >>= λ target → required "scope" V.asString fields >>= λ scope →
    required "rubric" V.asString fields >>= λ rubric → required "correctness" axis fields >>= λ correctness →
    required "usefulness" axis fields >>= λ usefulness →
    required "evidence_indices" (readArray (unsigned sizeMaximum)) fields >>= λ evidence →
    defaulted "item_ids" [] (readArray uuid) fields >>= λ items → required "rationale" V.asString fields >>= λ rationale →
    inj₂ (L.assessment target scope rubric rationale correctness usefulness evidence items))

  assessmentInput : V.Value → Fault ⊎ Input.Assessment
  assessmentInput = recordOf ("target" ∷ "scope" ∷ "rubric" ∷ "correctness" ∷ "usefulness" ∷ "evidence_indices" ∷
    "item_ids" ∷ "item_keys" ∷ "rationale" ∷ []) (λ fields →
    required "target" (target conversion) fields >>= λ target → required "scope" V.asString fields >>= λ scope →
    required "rubric" V.asString fields >>= λ rubric → required "correctness" axis fields >>= λ correctness →
    required "usefulness" axis fields >>= λ usefulness →
    required "evidence_indices" (readArray (unsigned sizeMaximum)) fields >>= λ evidence →
    defaulted "item_ids" [] (readArray uuid) fields >>= λ items → required "rationale" V.asString fields >>= λ rationale →
    defaulted "item_keys" [] (readArray V.asString) fields >>= λ names →
    inj₂ (Input.assessment (L.assessment target scope rubric rationale correctness usefulness evidence items) names))

  experience : V.Value → Fault ⊎ X.Experience
  experience = recordOf ("id" ∷ "project" ∷ "context" ∷ "action" ∷ "outcome" ∷ "source" ∷ "evidence" ∷
    "belief_ids" ∷ "pattern_id" ∷ "learning_items" ∷ "source_records" ∷ []) (λ fields →
    required "id" uuid fields >>= λ id → required "project" V.asString fields >>= λ project →
    required "context" V.asString fields >>= λ context → required "action" V.asString fields >>= λ action →
    required "outcome" outcome fields >>= λ outcome → required "source" Source.readProvenance fields >>= λ provenance →
    required "evidence" (readArray V.asString) fields >>= λ evidence →
    defaulted "belief_ids" [] (readArray uuid) fields >>= λ beliefs → optional "pattern_id" uuid fields >>= λ patternID →
    defaulted "learning_items" [] (readArray item) fields >>= λ items →
    defaulted "source_records" [] (readArray (Source.decode Objects.keepLast)) fields >>= λ sources →
    inj₂ (X.experience id project context action outcome provenance evidence beliefs patternID items sources))

  experienceInput : V.Value → Fault ⊎ Input.Experience
  experienceInput = recordOf ("id" ∷ "project" ∷ "context" ∷ "action" ∷ "outcome" ∷ "source" ∷ "evidence" ∷
    "belief_ids" ∷ "pattern_id" ∷ "learning_items" ∷ "source_records" ∷ []) (λ fields →
    required "id" uuid fields >>= λ id → required "project" V.asString fields >>= λ project →
    required "context" V.asString fields >>= λ context → required "action" V.asString fields >>= λ action →
    required "outcome" outcome fields >>= λ outcome → required "source" Source.readProvenance fields >>= λ provenance →
    required "evidence" (readArray V.asString) fields >>= λ evidence →
    defaulted "belief_ids" [] (readArray uuid) fields >>= λ beliefs → optional "pattern_id" uuid fields >>= λ patternID →
    defaulted "learning_items" [] (readArray itemInput) fields >>= λ items →
    defaulted "source_records" [] (readArray (Source.decode Objects.keepLast)) fields >>= λ sources →
    inj₂ (Input.experience id project context action outcome provenance evidence beliefs patternID items sources))

  feedback : V.Value → Fault ⊎ R.Feedback
  feedback = recordOf ("belief_id" ∷ "verdict" ∷ "weight" ∷ []) (λ fields →
    required "belief_id" uuid fields >>= λ id → required "verdict" verdict fields >>= λ verdict →
    required "weight" number fields >>= λ weight → inj₂ (R.feedback id verdict weight))

  link : V.Value → Fault ⊎ R.Link
  link = recordOf ("from_id" ∷ "to_id" ∷ "relation" ∷ "weight" ∷ []) (λ fields →
    required "from_id" uuid fields >>= λ from → required "to_id" uuid fields >>= λ to →
    required "relation" relation fields >>= λ relation → required "weight" number fields >>= λ weight →
    inj₂ (R.link from to relation weight))

  candidateFeedback : V.Value → Fault ⊎ R.CandidateFeedback
  candidateFeedback = recordOf ("target" ∷ "verdict" ∷ "weight" ∷ []) (λ fields →
    required "target" (target conversion) fields >>= λ target → required "verdict" verdict fields >>= λ verdict →
    required "weight" number fields >>= λ weight → inj₂ (R.candidateFeedback target verdict weight))

  candidateLink : V.Value → Fault ⊎ R.CandidateLink
  candidateLink = recordOf ("from" ∷ "to" ∷ "relation" ∷ "weight" ∷ []) (λ fields →
    required "from" (target conversion) fields >>= λ from → required "to" (target conversion) fields >>= λ to →
    required "relation" relation fields >>= λ relation → required "weight" number fields >>= λ weight →
    inj₂ (R.candidateLink from to relation weight))

  review : V.Value → Fault ⊎ R.Review
  review = recordOf ("experience_id" ∷ "experience_revision" ∷ "reviewer" ∷ "rationale" ∷ "feedback" ∷ "links" ∷
    "superseded_beliefs" ∷ "candidates" ∷ "candidate_feedback" ∷ "candidate_links" ∷ "assessments" ∷
    "extracted_items" ∷ "source_coverage" ∷ []) (λ fields →
    required "experience_id" uuid fields >>= λ id → required "experience_revision" i64 fields >>= λ revision →
    required "reviewer" V.asString fields >>= λ reviewer → required "rationale" V.asString fields >>= λ rationale →
    defaulted "feedback" [] (readArray feedback) fields >>= λ feedbacks →
    defaulted "links" [] (readArray link) fields >>= λ links →
    defaulted "superseded_beliefs" [] (readArray uuid) fields >>= λ superseded →
    defaulted "candidates" [] (readArray (Candidate.decode (readUUID conversion) Objects.keepLast)) fields >>= λ candidates →
    defaulted "candidate_feedback" [] (readArray candidateFeedback) fields >>= λ candidateFeedbacks →
    defaulted "candidate_links" [] (readArray candidateLink) fields >>= λ candidateLinks →
    defaulted "assessments" [] (readArray assessment) fields >>= λ assessments →
    defaulted "extracted_items" [] (readArray item) fields >>= λ extracted →
    defaulted "source_coverage" [] (readArray coverage) fields >>= λ coverage →
    inj₂ (R.review id revision reviewer rationale feedbacks links superseded candidates
      candidateFeedbacks candidateLinks assessments extracted coverage))

  reviewInput : V.Value → Fault ⊎ Input.Review
  reviewInput = recordOf ("experience_id" ∷ "experience_revision" ∷ "reviewer" ∷ "rationale" ∷ "feedback" ∷ "links" ∷
    "superseded_beliefs" ∷ "candidates" ∷ "candidate_feedback" ∷ "candidate_links" ∷ "assessments" ∷
    "extracted_items" ∷ "source_coverage" ∷ []) (λ fields →
    required "experience_id" uuid fields >>= λ id → required "experience_revision" i64 fields >>= λ revision →
    required "reviewer" V.asString fields >>= λ reviewer → required "rationale" V.asString fields >>= λ rationale →
    defaulted "feedback" [] (readArray feedback) fields >>= λ feedbacks →
    defaulted "links" [] (readArray link) fields >>= λ links →
    defaulted "superseded_beliefs" [] (readArray uuid) fields >>= λ superseded →
    defaulted "candidates" [] (readArray (Candidate.decode (readUUID conversion) Objects.keepLast)) fields >>= λ candidates →
    defaulted "candidate_feedback" [] (readArray candidateFeedback) fields >>= λ candidateFeedbacks →
    defaulted "candidate_links" [] (readArray candidateLink) fields >>= λ candidateLinks →
    defaulted "assessments" [] (readArray assessmentInput) fields >>= λ assessments →
    defaulted "extracted_items" [] (readArray itemInput) fields >>= λ extracted →
    defaulted "source_coverage" [] (readArray coverage) fields >>= λ coverage →
    inj₂ (Input.review id revision reviewer rationale feedbacks links superseded candidates
      candidateFeedbacks candidateLinks assessments extracted coverage))
