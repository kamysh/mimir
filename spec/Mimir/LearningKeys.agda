{-# OPTIONS --safe #-}
-- Canonical comparison projection, not a serializer or a rewrite of stored
-- requests. Typed retries compare finite numeric values, preserving exact text.
module Mimir.LearningKeys where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (toℕ)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Mimir.SemanticKey using (Key; natural; uuid; integer; text; real; fields)
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
item i = fields (uuid (LearningItem.identity i) ∷ optional text (LearningItem.localKey i) ∷ kind (LearningItem.kind i) ∷
  text (LearningItem.reference i) ∷ text (LearningItem.actor i) ∷ text (LearningItem.statement i) ∷
  text (LearningItem.conditions i) ∷ many prediction (LearningItem.predictions i) ∷ [])

target : Target → Key
target (existing id) = uuid id
target (candidate name) = text name

assessment : Assessment → Key
assessment a = fields (target (Assessment.target a) ∷ text (Assessment.scope a) ∷
  text (Assessment.rubric a) ∷ axis (Assessment.correctness a) ∷ axis (Assessment.usefulness a) ∷
  many natural (Assessment.evidenceIndices a) ∷ many uuid (Assessment.itemIDs a) ∷
  text (Assessment.rationale a) ∷ [])

outcome : Outcome → Key
outcome success = natural 0
outcome failure = natural 1
outcome unknown = natural 2

experience : Experience → Key
experience e = fields (uuid (Experience.identity e) ∷ text (Experience.project e) ∷
  text (Experience.context e) ∷ text (Experience.action e) ∷ outcome (Experience.outcome e) ∷
  provenance (Experience.provenance e) ∷ many text (Experience.evidence e) ∷
  many uuid (Experience.beliefIDs e) ∷ optional uuid (Experience.patternID e) ∷
  many item (Experience.items e) ∷ many source (Experience.sources e) ∷ [])

memory : Memory → Key
memory fact = natural 0
memory experiential = natural 1
memory working = natural 2

candidateValue : Candidate → Key
candidateValue (belief name content mode source) = fields
  (natural 0 ∷ text name ∷ text content ∷ memory mode ∷ optional uuid source ∷ [])
candidateValue (patternCandidate name situation approach) = fields
  (natural 1 ∷ text name ∷ text situation ∷ text approach ∷ [])

verdict : Verdict → Key
verdict support = natural 0
verdict defeat = natural 1

feedback : Feedback → Key
feedback f = fields (uuid (Feedback.beliefID f) ∷ verdict (Feedback.verdict f) ∷ number (Feedback.weight f) ∷ [])

link : Link → Key
link l = fields (uuid (Link.from l) ∷ uuid (Link.to l) ∷
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

review : Review → Key
review r = fields (uuid (Review.experienceID r) ∷ integer (Review.experienceRevision r) ∷
  text (Review.reviewer r) ∷ text (Review.rationale r) ∷ many feedback (Review.feedbacks r) ∷
  many link (Review.links r) ∷ many uuid (Review.superseded r) ∷
  many candidateValue (Review.candidates r) ∷ many candidateFeedback (Review.candidateFeedbacks r) ∷
  many candidateLink (Review.candidateLinks r) ∷ many assessment (Review.assessments r) ∷
  many item (Review.extracted r) ∷ many coverage (Review.coverage r) ∷ [])
