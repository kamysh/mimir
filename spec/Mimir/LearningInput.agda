{-# OPTIONS --safe #-}
-- Incoming items have not yet received their canonical database identity.
-- Request and stored-response types are deliberately separate: an omitted ID
-- remains omitted until the locked allocation operation observes PostgreSQL.
module Mimir.LearningInput where

open import Data.List using (List; []; _∷_; _++_; map; mapMaybe)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.List.Relation.Unary.All using (All)
open import Mimir.Validation
import Mimir.Collections as Collections
open import Mimir.SourceReview using (_≟Text_)
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
    identity : Maybe ℕ
    localKey : Maybe Text
    kind : L.Kind
    reference actor statement conditions : Text
    predictions : List L.Prediction

canonicalItem : ℕ → Item → L.LearningItem
canonicalItem assigned input = L.learningItem assigned (Item.localKey input)
  (Item.kind input) (Item.reference input) (Item.actor input)
  (Item.statement input) (Item.conditions input) (Item.predictions input)

record Assessment : Set where
  constructor assessment
  field value : L.Assessment; itemKeys : List Text

canonicalAssessment : Assessment → List ℕ → L.Assessment
canonicalAssessment input resolved = record (Assessment.value input)
  { itemIDs = L.Assessment.itemIDs (Assessment.value input) ++ resolved }

record Experience : Set where
  constructor experience
  field
    identity : ℕ
    project context action : Text
    outcome : X.Outcome
    provenance : Source.Provenance
    evidence : List Text
    beliefIDs : List ℕ
    patternID : Maybe ℕ
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
    experienceID : ℕ
    experienceRevision : ℤ
    reviewer rationale : Text
    feedbacks : List R.Feedback
    links : List R.Link
    superseded : List ℕ
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

-- These checks retain optional identities and local keys exactly as supplied.
HasItemReference : Item → Set
HasItemReference value with Item.identity value | Item.localKey value
... | nothing | nothing = ⊥
... | _ | _ = ⊤

checkItemReference : ∀ value → Checked (HasItemReference value)
checkItemReference value with Item.identity value | Item.localKey value
... | nothing | nothing = rejected
  (fault (key "key" ∷ []) missingReference "Supply a local item key or an existing item ID; do not invent a database identity.") (λ ())
... | just _ | _ = accepted tt
... | nothing | just _ = accepted tt

OptionalKeyValid : Maybe Text → Set
OptionalKeyValid nothing = ⊤
OptionalKeyValid (just name) = Candidates.Trimmed name

checkOptionalKey : ∀ name → Checked (OptionalKeyValid name)
checkOptionalKey nothing = accepted tt
checkOptionalKey (just name) = Candidates.checkTrimmed name

ItemValid : Item → Set
ItemValid value = HasItemReference value ×
  (OptionalKeyValid (Item.localKey value) ×
    L.ItemFieldsValid (Item.reference value) (Item.actor value)
      (Item.statement value) (Item.conditions value) (Item.predictions value))

validateItem : ∀ value → Checked (ItemValid value)
validateItem value = combine (checkItemReference value)
  (combine (at (key "key") (checkOptionalKey (Item.localKey value)))
    (L.validateItemFields (Item.reference value) (Item.actor value)
      (Item.statement value) (Item.conditions value) (Item.predictions value)))

module TextKeys = Collections.Equality Text _≟Text_

ItemsValid : List Item → Set
ItemsValid values = L.UniqueIDs (mapMaybe Item.identity values) ×
  (TextKeys.Unique (mapMaybe Item.localKey values) × All ItemValid values)

validateItems : ∀ values → Checked (ItemsValid values)
validateItems values = combine (L.checkIDs (mapMaybe Item.identity values))
  (combine (TextKeys.checkUnique (mapMaybe Item.localKey values)) (allChecked validateItem values))

AssessmentKeysValid : Assessment → Set
AssessmentKeysValid value = All Candidates.Trimmed (Assessment.itemKeys value) ×
  TextKeys.Unique (Assessment.itemKeys value)

validateAssessmentKeys : ∀ value → Checked (AssessmentKeysValid value)
validateAssessmentKeys value = at (key "item_keys")
  (combine (allChecked Candidates.checkTrimmed (Assessment.itemKeys value))
    (TextKeys.checkUnique (Assessment.itemKeys value)))

-- The reused header/contribution validator never reads extracted-item IDs.
-- Actual assessment values are retained, and their local keys are checked
-- separately. This introduces no placeholder database identity.
reviewHeaderView : Review → R.Review
reviewHeaderView value = canonicalReview value [] (map Assessment.value (Review.assessments value))

ReviewValid : Review → Set
ReviewValid value = ItemsValid (Review.extracted value) ×
  (All AssessmentKeysValid (Review.assessments value) × R.ReviewValid (reviewHeaderView value))

validateReview : ∀ value → Checked (ReviewValid value)
validateReview value = combine (at (key "extracted_items") (validateItems (Review.extracted value)))
  (combine (at (key "assessments") (allChecked validateAssessmentKeys (Review.assessments value)))
    (R.validateReview (reviewHeaderView value)))
