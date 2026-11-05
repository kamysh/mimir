{-# OPTIONS --safe #-}
-- Structural review validation. Wire decoding and
-- database target existence are separate obligations, not implicit premises.
module Mimir.ReviewSchema where

open import Data.Empty using (⊥)
open import Data.Integer using (ℤ; +_)
import Data.Integer.Properties as Integer
open import Data.List using (List; []; _∷_; map; length; _++_; concatMap)
open import Data.List.Properties using (≡-dec)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; _+_; _≤_; _≤?_; _≟_; _⊓_; _⊔_)
open import Data.Nat.Properties using (⊓-comm; ⊔-comm)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational using (0ℚ; 1ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Mimir.Text using (Text)
open import Mimir.Binary64 using (Number)
open import Mimir.NumericValidation using (Between; checkBetween)
open import Mimir.Validation hiding (Feedback; feedback)
open import Mimir.Collections
open import Mimir.SourceReview using (_≟Text_; Coverage)
open import Mimir.LearningSchema using (Target; existing; candidate; Assessment;
  AssessmentValid; validateAssessment; LearningItem)
open import Mimir.LearningCandidates using (Candidate; candidateKey; Valid; validate;
  TargetValid; validateTarget; checkNonblank; targetEqual; module Targets)

data Verdict : Set where support defeat : Verdict
data Relation : Set where supports defeats causes contradicts : Relation

record Feedback : Set where
  constructor feedback
  field beliefID : ℕ; verdict : Verdict; weight : Number

record Link : Set where
  constructor link
  field from to : ℕ; relation : Relation; weight : Number

record CandidateFeedback : Set where
  constructor candidateFeedback
  field target : Target; verdict : Verdict; weight : Number

record CandidateLink : Set where
  constructor candidateLink
  field from to : Target; relation : Relation; weight : Number

record Review : Set where
  constructor review
  field
    experienceID : ℕ
    experienceRevision : ℤ
    reviewer rationale : Text
    feedbacks : List Feedback
    links : List Link
    superseded : List ℕ
    candidates : List Candidate
    candidateFeedbacks : List CandidateFeedback
    candidateLinks : List CandidateLink
    assessments : List Assessment
    extracted : List LearningItem
    coverage : List Coverage

module IDs = Equality ℕ _≟_
module TextKeys = Equality Text _≟Text_
module LinkKeys = Equality (List ℕ) (≡-dec _≟_)

AssessmentKey = Target × (Text × Text)
module AssessmentKeys = Equality AssessmentKey
  (pairEqual targetEqual (pairEqual _≟Text_ _≟Text_))

assessmentKey : Assessment → AssessmentKey
assessmentKey a = Assessment.target a , Assessment.scope a , Assessment.rubric a

relationCode : Relation → ℕ
relationCode supports = 0
relationCode defeats = 1
relationCode causes = 2
relationCode contradicts = 3

linkKey : Link → List ℕ
linkKey (link from to contradicts weight) = (from ⊓ to) ∷ (from ⊔ to) ∷ 3 ∷ []
linkKey (link from to supports weight) = from ∷ to ∷ 0 ∷ []
linkKey (link from to defeats weight) = from ∷ to ∷ 1 ∷ []
linkKey (link from to causes weight) = from ∷ to ∷ 2 ∷ []

contradictionReversalKey : ∀ from to weight₁ weight₂ →
  linkKey (link from to contradicts weight₁) ≡ linkKey (link to from contradicts weight₂)
contradictionReversalKey from to weight₁ weight₂ rewrite ⊓-comm from to | ⊔-comm from to = refl

Probability : Number → Set
Probability = Between 0ℚ 1ℚ

checkProbability : ∀ value → Checked (Probability value)
checkProbability = checkBetween 0ℚ 1ℚ

LinkValid : Link → Set
LinkValid l = Probability (Link.weight l) × Link.from l ≢ Link.to l

checkLink : ∀ l → Checked (LinkValid l)
checkLink l = combine (at (key "weight") (checkProbability (Link.weight l)))
  (check (fault [] unsupportedCombination "self links are not permitted")
    (negate (Link.from l ≟ Link.to l)))

CandidateFeedbackValid : List Candidate → CandidateFeedback → Set
CandidateFeedbackValid cs f = Probability (CandidateFeedback.weight f) × TargetValid cs (CandidateFeedback.target f)

checkCandidateFeedback : ∀ cs f → Checked (CandidateFeedbackValid cs f)
checkCandidateFeedback cs f = combine
  (at (key "weight") (checkProbability (CandidateFeedback.weight f)))
  (at (key "target") (validateTarget cs (CandidateFeedback.target f)))

CandidateLinkValid : List Candidate → CandidateLink → Set
CandidateLinkValid cs l = Probability (CandidateLink.weight l) ×
  (TargetValid cs (CandidateLink.from l) × TargetValid cs (CandidateLink.to l))

checkCandidateLink : ∀ cs l → Checked (CandidateLinkValid cs l)
checkCandidateLink cs l = combine
  (at (key "weight") (checkProbability (CandidateLink.weight l)))
  (combine (at (key "from") (validateTarget cs (CandidateLink.from l)))
    (at (key "to") (validateTarget cs (CandidateLink.to l))))

linkTargets : Link → List Target
linkTargets l = existing (Link.from l) ∷ existing (Link.to l) ∷ []

candidateLinkTargets : CandidateLink → List Target
candidateLinkTargets l = CandidateLink.from l ∷ CandidateLink.to l ∷ []

legacyTargets : Review → List Target
legacyTargets r = map (λ f → existing (Feedback.beliefID f)) (Review.feedbacks r) ++
  concatMap linkTargets (Review.links r) ++
  map CandidateFeedback.target (Review.candidateFeedbacks r) ++
  concatMap candidateLinkTargets (Review.candidateLinks r)

-- This is exactly the overlap rule: links count as legacy contributions at
-- both endpoints; target/scope/rubric define a unique typed assessment.
TypedValid : Review → Assessment → Set
TypedValid r a = AssessmentValid a ×
  (TargetValid (Review.candidates r) (Assessment.target a) ×
    Targets.Absent (Assessment.target a) (legacyTargets r))

checkTyped : ∀ r a → Checked (TypedValid r a)
checkTyped r a = combine (validateAssessment a)
  (combine (at (key "target") (validateTarget (Review.candidates r) (Assessment.target a)))
    (check (fault [] unsupportedCombination "typed and legacy evidence overlap")
      (Targets.absent? (Assessment.target a) (legacyTargets r))))

typedNeverLegacy : ∀ r a → TypedValid r a →
  Targets.Present (Assessment.target a) (legacyTargets r) → ⊥
typedNeverLegacy r a (valid , target , absent) present = Targets.presentAbsentContradiction present absent



CandidatesValid : Review → Set
CandidatesValid r = All Valid (Review.candidates r) ×
  (TextKeys.Unique (map candidateKey (Review.candidates r)) ×
  (All (CandidateFeedbackValid (Review.candidates r)) (Review.candidateFeedbacks r) ×
    All (CandidateLinkValid (Review.candidates r)) (Review.candidateLinks r)))

checkCandidates : ∀ r → Checked (CandidatesValid r)
checkCandidates r = combine (at (key "candidates") (allChecked validate (Review.candidates r)))
  (combine (at (key "candidates") (TextKeys.checkUnique (map candidateKey (Review.candidates r))))
  (combine (at (key "candidate_feedback") (allChecked (checkCandidateFeedback (Review.candidates r)) (Review.candidateFeedbacks r)))
    (at (key "candidate_links") (allChecked (checkCandidateLink (Review.candidates r)) (Review.candidateLinks r)))))

LegacyValid : Review → Set
LegacyValid r = All LinkValid (Review.links r) ×
  (LinkKeys.Unique (map linkKey (Review.links r)) ×
  (All (λ f → Probability (Feedback.weight f)) (Review.feedbacks r) ×
    IDs.Unique (map Feedback.beliefID (Review.feedbacks r))))

checkLegacy : ∀ r → Checked (LegacyValid r)
checkLegacy r = combine (at (key "links") (allChecked checkLink (Review.links r)))
  (combine (at (key "links") (LinkKeys.checkUnique (map linkKey (Review.links r))))
  (combine (at (key "feedback") (allChecked (λ f → checkProbability (Feedback.weight f)) (Review.feedbacks r)))
    (at (key "feedback") (IDs.checkUnique (map Feedback.beliefID (Review.feedbacks r))))))

ReviewValid : Review → Set
ReviewValid r = (+ 0 Data.Integer.< Review.experienceRevision r) ×
  (Mimir.Text.Nonblank (Review.reviewer r) ×
  (Mimir.Text.Nonblank (Review.rationale r) ×
  (CandidatesValid r × (LegacyValid r ×
  (All (TypedValid r) (Review.assessments r) ×
    AssessmentKeys.Unique (map assessmentKey (Review.assessments r)))))))

validateReview : ∀ r → Checked (ReviewValid r)
validateReview r = combine
  (at (key "experience_revision") (check (fault [] staleRevision "experience revision must be positive")
    ((+ 0) Integer.<? Review.experienceRevision r)))
  (combine (at (key "reviewer") (checkNonblank (Review.reviewer r)))
  (combine (at (key "rationale") (checkNonblank (Review.rationale r)))
  (combine (checkCandidates r) (combine (checkLegacy r)
  (combine (at (key "assessments") (allChecked (checkTyped r) (Review.assessments r)))
    (at (key "assessments") (AssessmentKeys.checkUnique (map assessmentKey (Review.assessments r)))))))))

validReviewNeverRejected : ∀ r → ReviewValid r → reported (validateReview r) ≡ []
validReviewNeverRejected r = noFalseRejection (validateReview r)
