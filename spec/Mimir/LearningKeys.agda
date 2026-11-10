{-# OPTIONS --safe #-}
-- Canonical comparison projection, not a serializer or a rewrite of stored
-- requests. Typed retries compare finite numeric values, preserving exact text.
module Mimir.LearningKeys where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (toℕ)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Mimir.SemanticKey using (Key; natural; integer; text; real; fields)
open import Mimir.Binary64 using (Number; finite; nonfinite; FiniteNumber; value;
  Word; Sign; positive; negative)
open import Mimir.NumericValidation using (Axis)
open import Mimir.SourceSchema using (Source; Provenance; userFeedback; agentReport; toolResult)
open import Mimir.SourceReview using (Coverage; Status; complete; unresolved)
open import Mimir.LearningSchema using (Prediction; LearningItem; Kind; estimate; decision; suggestion;
  Assessment; Target; existing; candidate)
open import Mimir.LearningCandidates using (Candidate; belief; patternCandidate; Memory; fact; experiential; working)
open import Mimir.ExperienceSchema using (Experience; Outcome; success; failure; unknown)
open import Mimir.ReviewSchema using (Review; Feedback; Link; CandidateFeedback; CandidateLink;
  Verdict; support; defeat; relationCode)
import Mimir.DocumentStore as Documents
import Mimir.LearningInput as Input

optional : ∀ {A : Set} → (A → Key) → Maybe A → Key
optional encode nothing = fields []
optional encode (just x) = fields (encode x ∷ [])

many : ∀ {A : Set} → (A → Key) → List A → Key
many encode xs = fields (map encode xs)

boolean : Bool → Key
boolean false = natural 0
boolean true = natural 1

sign : Sign → Key
sign positive = natural 0
sign negative = natural 1

number : Number → Key
number (finite n) = real (value n)
-- Invalid inputs are rejected before retry comparison. Retain their bits in
-- this total projection rather than identifying all invalid numbers.
number (nonfinite w proof) = fields
  (sign (Word.sign w) ∷ natural (toℕ (Word.exponent w)) ∷ natural (toℕ (Word.fraction w)) ∷ [])

axis : Axis → Key
axis a = fields (optional number (Axis.estimate a) ∷ number (Axis.weight a) ∷ [])

provenance : Provenance → Key
provenance userFeedback = natural 0
provenance agentReport = natural 1
provenance toolResult = natural 2

source : Source → Key
source s = fields (text (Source.reference s) ∷ text (Source.actor s) ∷
  provenance (Source.provenance s) ∷ text (Source.text s) ∷ optional text (Source.recordedAt s) ∷ [])

kind : Kind → Key
kind estimate = natural 0
kind decision = natural 1
kind suggestion = natural 2

prediction : Prediction → Key
prediction p = fields (text (Prediction.quantity p) ∷ number (Prediction.point p) ∷
  text (Prediction.unit p) ∷ optional number (Prediction.probability p) ∷
  optional number (Prediction.lower p) ∷ optional number (Prediction.upper p) ∷
  text (Prediction.horizon p) ∷ text (Prediction.recordedAt p) ∷ boolean (Prediction.inferred p) ∷ [])

item : LearningItem → Key
item i = fields (natural (LearningItem.identity i) ∷ optional text (LearningItem.localKey i) ∷ kind (LearningItem.kind i) ∷
  text (LearningItem.reference i) ∷ text (LearningItem.actor i) ∷ text (LearningItem.statement i) ∷
  text (LearningItem.conditions i) ∷ many prediction (LearningItem.predictions i) ∷ [])

target : Target → Key
target (existing id) = natural id
target (candidate name) = text name

assessment : Assessment → Key
assessment a = fields (target (Assessment.target a) ∷ text (Assessment.scope a) ∷
  text (Assessment.rubric a) ∷ axis (Assessment.correctness a) ∷ axis (Assessment.usefulness a) ∷
  many natural (Assessment.evidenceIndices a) ∷ many natural (Assessment.itemIDs a) ∷
  text (Assessment.rationale a) ∷ [])

outcome : Outcome → Key
outcome success = natural 0
outcome failure = natural 1
outcome unknown = natural 2

experience : Experience → Key
experience e = fields (natural (Experience.identity e) ∷ text (Experience.project e) ∷
  text (Experience.context e) ∷ text (Experience.action e) ∷ outcome (Experience.outcome e) ∷
  provenance (Experience.provenance e) ∷ many text (Experience.evidence e) ∷
  many natural (Experience.beliefIDs e) ∷ optional natural (Experience.patternID e) ∷
  many item (Experience.items e) ∷ many source (Experience.sources e) ∷ [])

memory : Memory → Key
memory fact = natural 0
memory experiential = natural 1
memory working = natural 2

candidateValue : Candidate → Key
candidateValue (belief name content mode cited) = fields
  (natural 0 ∷ text name ∷ text content ∷ memory mode ∷ many citation cited ∷ [])
  where
  citation : Documents.Citation → Key
  citation value = fields (natural (Documents.Citation.chunk value) ∷ text (Documents.Citation.document value) ∷
    text (Documents.Citation.quotation value) ∷ text (Documents.Citation.explanation value) ∷ [])
candidateValue (patternCandidate name situation approach) = fields
  (natural 1 ∷ text name ∷ text situation ∷ text approach ∷ [])

verdict : Verdict → Key
verdict support = natural 0
verdict defeat = natural 1

feedback : Feedback → Key
feedback f = fields (natural (Feedback.beliefID f) ∷ verdict (Feedback.verdict f) ∷ number (Feedback.weight f) ∷ [])

link : Link → Key
link l = fields (natural (Link.from l) ∷ natural (Link.to l) ∷
  natural (relationCode (Link.relation l)) ∷ number (Link.weight l) ∷ [])

candidateFeedback : CandidateFeedback → Key
candidateFeedback f = fields (target (CandidateFeedback.target f) ∷
  verdict (CandidateFeedback.verdict f) ∷ number (CandidateFeedback.weight f) ∷ [])

candidateLink : CandidateLink → Key
candidateLink l = fields (target (CandidateLink.from l) ∷ target (CandidateLink.to l) ∷
  natural (relationCode (CandidateLink.relation l)) ∷ number (CandidateLink.weight l) ∷ [])

status : Status → Key
status complete = natural 0
status unresolved = natural 1

coverage : Coverage → Key
coverage c = fields (text (Coverage.reference c) ∷ status (Coverage.status c) ∷ text (Coverage.reason c) ∷ [])

-- Canonical rows serialize item IDs as present optional fields and have no
-- unresolved assessment item_keys. This also represents the native fallback
-- to an applied legacy payload when its separate request column is NULL.
recordedItem : LearningItem → Key
recordedItem i = fields (optional natural (just (LearningItem.identity i)) ∷ optional text (LearningItem.localKey i) ∷ kind (LearningItem.kind i) ∷
  text (LearningItem.reference i) ∷ text (LearningItem.actor i) ∷ text (LearningItem.statement i) ∷
  text (LearningItem.conditions i) ∷ many prediction (LearningItem.predictions i) ∷ [])

recordedAssessment : Assessment → Key
recordedAssessment a = fields (assessment a ∷ fields [] ∷ [])

review : Review → Key
review r = fields (natural (Review.experienceID r) ∷ integer (Review.experienceRevision r) ∷
  text (Review.reviewer r) ∷ text (Review.rationale r) ∷ many feedback (Review.feedbacks r) ∷
  many link (Review.links r) ∷ many natural (Review.superseded r) ∷
  many candidateValue (Review.candidates r) ∷ many candidateFeedback (Review.candidateFeedbacks r) ∷
  many candidateLink (Review.candidateLinks r) ∷ many recordedAssessment (Review.assessments r) ∷
  many recordedItem (Review.extracted r) ∷ many coverage (Review.coverage r) ∷ [])

-- Request identity retains what was submitted before PostgreSQL fills IDs
-- and resolves item_keys. Equal applied reviews are not necessarily retries
-- of the same submitted declaration.
inputItem : Input.Item → Key
inputItem i = fields (optional natural (Input.Item.identity i) ∷ optional text (Input.Item.localKey i) ∷
  kind (Input.Item.kind i) ∷ text (Input.Item.reference i) ∷ text (Input.Item.actor i) ∷
  text (Input.Item.statement i) ∷ text (Input.Item.conditions i) ∷ many prediction (Input.Item.predictions i) ∷ [])

inputAssessment : Input.Assessment → Key
inputAssessment a = fields (assessment (Input.Assessment.value a) ∷ many text (Input.Assessment.itemKeys a) ∷ [])

reviewInput : Input.Review → Key
reviewInput r = fields (natural (Input.Review.experienceID r) ∷ integer (Input.Review.experienceRevision r) ∷
  text (Input.Review.reviewer r) ∷ text (Input.Review.rationale r) ∷ many feedback (Input.Review.feedbacks r) ∷
  many link (Input.Review.links r) ∷ many natural (Input.Review.superseded r) ∷
  many candidateValue (Input.Review.candidates r) ∷ many candidateFeedback (Input.Review.candidateFeedbacks r) ∷
  many candidateLink (Input.Review.candidateLinks r) ∷ many inputAssessment (Input.Review.assessments r) ∷
  many inputItem (Input.Review.extracted r) ∷ many coverage (Input.Review.coverage r) ∷ [])

numericComparisonIsSemantic : ∀ left right → value left ≡ value right → number (finite left) ≡ number (finite right)
numericComparisonIsSemantic left right = cong real

numericComparisonReflectsValue : ∀ left right → number (finite left) ≡ number (finite right) → value left ≡ value right
numericComparisonReflectsValue left right = Mimir.SemanticKey.realFaithful (value left) (value right)
