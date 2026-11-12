{-# OPTIONS --safe #-}
-- Incoming items have not yet received their canonical database identity.
-- Request and stored-response types are deliberately separate: an omitted ID
-- remains omitted until the locked allocation operation observes PostgreSQL.
module Mimir.LearningInput where

open import Data.List using (List; _++_)
open import Data.Maybe using (Maybe)
open import Mimir.UUIDGroups using (UUID)
open import Data.Integer using (ℤ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.LearningSchema as L
import Mimir.ExperienceSchema as X
import Mimir.ReviewSchema as R
import Mimir.SourceSchema as Source
import Mimir.SourceReview as Coverage
import Mimir.LearningCandidates as Candidates

record Item : Set where
  constructor item
  field
    identity : Maybe UUID
    localKey : Maybe Text
    kind : L.Kind
    reference actor statement conditions : Text
    predictions : List L.Prediction

canonicalItem : UUID → Item → L.LearningItem
canonicalItem assigned input = L.learningItem assigned (Item.localKey input)
  (Item.kind input) (Item.reference input) (Item.actor input)
  (Item.statement input) (Item.conditions input) (Item.predictions input)

record Assessment : Set where
  constructor assessment
  field value : L.Assessment; itemKeys : List Text

canonicalAssessment : Assessment → List UUID → L.Assessment
canonicalAssessment input resolved = record (Assessment.value input)
  { itemIDs = L.Assessment.itemIDs (Assessment.value input) ++ resolved }

record Experience : Set where
  constructor experience
  field
    identity : UUID
    project context action : Text
    outcome : X.Outcome
    provenance : Source.Provenance
    evidence : List Text
    beliefIDs : List UUID
    patternID : Maybe UUID
    items : List Item
    sources : List Source.Source

canonicalExperience : Experience → List L.LearningItem → X.Experience
canonicalExperience input assigned = X.experience (Experience.identity input)
  (Experience.project input) (Experience.context input) (Experience.action input)
  (Experience.outcome input) (Experience.provenance input) (Experience.evidence input)
  (Experience.beliefIDs input) (Experience.patternID input) assigned (Experience.sources input)

record Review : Set where
  constructor review
  field
    experienceID : UUID
    experienceRevision : ℤ
    reviewer rationale : Text
    feedbacks : List R.Feedback
    links : List R.Link
    superseded : List UUID
    candidates : List Candidates.Candidate
    candidateFeedbacks : List R.CandidateFeedback
    candidateLinks : List R.CandidateLink
    assessments : List Assessment
    extracted : List Item
    coverage : List Coverage.Coverage

canonicalReview : Review → List L.LearningItem → List L.Assessment → R.Review
canonicalReview input assigned resolved = R.review (Review.experienceID input)
  (Review.experienceRevision input) (Review.reviewer input) (Review.rationale input)
  (Review.feedbacks input) (Review.links input) (Review.superseded input)
  (Review.candidates input) (Review.candidateFeedbacks input) (Review.candidateLinks input)
  resolved assigned (Review.coverage input)

canonicalItemKeepsKey : ∀ assigned input →
  L.LearningItem.localKey (canonicalItem assigned input) ≡ Item.localKey input
canonicalItemKeepsKey assigned input = refl

canonicalItemUsesAssignedID : ∀ assigned input →
  L.LearningItem.identity (canonicalItem assigned input) ≡ assigned
canonicalItemUsesAssignedID assigned input = refl

experienceRetainsAssignments : ∀ input assigned →
  X.Experience.items (canonicalExperience input assigned) ≡ assigned
experienceRetainsAssignments input assigned = refl

reviewRetainsAssignments : ∀ input assigned resolved →
  R.Review.extracted (canonicalReview input assigned resolved) ≡ assigned
reviewRetainsAssignments input assigned resolved = refl

reviewRetainsResolvedReferences : ∀ input assigned resolved →
  R.Review.assessments (canonicalReview input assigned resolved) ≡ resolved
reviewRetainsResolvedReferences input assigned resolved = refl
