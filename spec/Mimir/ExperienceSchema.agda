{-# OPTIONS --safe #-}
-- Core experience contract and composition of source/assessment validation.
-- The 64 KiB serialized JSON limit belongs to the wire encoder contract.
module Mimir.ExperienceSchema where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map; _++_; concatMap)
open import Data.List.Properties using (≡-dec)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text
open import Mimir.Validation
open import Mimir.Collections
open import Mimir.SourceSchema using (Source; Provenance; SourcesValid; validateSources)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.LearningCandidates using (checkNonblank)
import Mimir.LearningSchema as Items
import Mimir.SourceReview as Sources
import Mimir.ReviewSchema as Reviews

data Outcome : Set where success failure unknown : Outcome

record Experience : Set where
  constructor experience
  field
    identity : ℕ
    project context action : Text
    outcome : Outcome
    provenance : Provenance
    evidence : List Text
    beliefIDs : List ℕ
    patternID : Maybe ℕ
    items : List Items.LearningItem
    sources : List Source

EvidenceReferences : List Source → List Text → Set
EvidenceReferences [] evidence = ⊤
EvidenceReferences sources@(_ ∷ _) evidence = map Source.reference sources ≡ evidence

checkEvidenceReferences : ∀ sources evidence → Checked (EvidenceReferences sources evidence)
checkEvidenceReferences [] evidence = accepted tt
checkEvidenceReferences sources@(_ ∷ _) evidence = check
  (fault [] missingReference "source evidence indices must correspond to source references")
  (≡-dec _≟Text_ (map Source.reference sources) evidence)

HasEvidence : List Text → Set
HasEvidence = Any Nonblank

OutcomeEvidence : Outcome → List Text → Set
OutcomeEvidence unknown evidence = ⊤
OutcomeEvidence success evidence = HasEvidence evidence
OutcomeEvidence failure evidence = HasEvidence evidence

checkHasEvidence : ∀ evidence → Checked (HasEvidence evidence)
checkHasEvidence evidence = check (fault [] missingEvidence "a known outcome requires evidence")
  (any? nonblank? evidence)

checkOutcomeEvidence : ∀ outcome evidence → Checked (OutcomeEvidence outcome evidence)
checkOutcomeEvidence unknown evidence = accepted tt
checkOutcomeEvidence success evidence = checkHasEvidence evidence
checkOutcomeEvidence failure evidence = checkHasEvidence evidence

Valid : Experience → Set
Valid e = Items.ItemsValid (Experience.items e) ×
  (SourcesValid (Experience.sources e) ×
  (EvidenceReferences (Experience.sources e) (Experience.evidence e) ×
  (Nonblank (Experience.project e) ×
  (Nonblank (Experience.context e) ×
  (Nonblank (Experience.action e) ×
  (atMost 32 (Experience.evidence e) ×
  (atMost 64 (Experience.beliefIDs e) ×
    OutcomeEvidence (Experience.outcome e) (Experience.evidence e))))))))

validate : ∀ e → Checked (Valid e)
validate e = combine (at (key "learning_items") (Items.validateItems (Experience.items e)))
  (combine (validateSources (Experience.sources e))
  (combine (checkEvidenceReferences (Experience.sources e) (Experience.evidence e))
  (combine (at (key "project") (checkNonblank (Experience.project e)))
  (combine (at (key "context") (checkNonblank (Experience.context e)))
  (combine (at (key "action") (checkNonblank (Experience.action e)))
  (combine (at (key "evidence") (checkCount 32 (Experience.evidence e)))
  (combine (at (key "belief_ids") (checkCount 64 (Experience.beliefIDs e)))
    (checkOutcomeEvidence (Experience.outcome e) (Experience.evidence e)))))))))

hasLegacy : Reviews.Review → Bool
hasLegacy r with Reviews.Review.feedbacks r | Reviews.Review.links r |
  Reviews.Review.candidateFeedbacks r | Reviews.Review.candidateLinks r
... | [] | [] | [] | [] = false
... | _ | _ | _ | _ = true

sourceReview : Reviews.Review → Sources.Review
sourceReview r = Sources.review (Reviews.Review.coverage r)
  (map Items.sourceProjection (Reviews.Review.extracted r))
  (concatMap Items.Assessment.itemIDs (Reviews.Review.assessments r)) (hasLegacy r)

itemIDs : Experience → List ℕ
itemIDs e = map Items.LearningItem.identity (Experience.items e)

allItemIDs : Experience → Reviews.Review → List ℕ
allItemIDs e r = itemIDs e ++ map Items.LearningItem.identity (Reviews.Review.extracted r)

ReviewSourcesValid : Experience → Reviews.Review → Set
ReviewSourcesValid e r = Items.ItemsValid (Reviews.Review.extracted r) ×
  (Sources.ReviewIntegrity (Experience.sources e) (itemIDs e) (sourceReview r) ×
    All (Items.SourceValid (Experience.provenance e) (Experience.sources e)
      (Experience.evidence e) (allItemIDs e r)) (Reviews.Review.assessments r))

validateReviewSources : ∀ e r → Checked (ReviewSourcesValid e r)
validateReviewSources e r = combine
  (at (key "extracted_items") (Items.validateItems (Reviews.Review.extracted r)))
  (combine (Sources.validateReviewIntegrity (Experience.sources e) (itemIDs e) (sourceReview r))
    (at (key "assessments") (allChecked
      (Items.validateSource (Experience.provenance e) (Experience.sources e)
        (Experience.evidence e) (allItemIDs e r)) (Reviews.Review.assessments r))))

validExperienceNeverRejected : ∀ e → Valid e → reported (validate e) ≡ []
validExperienceNeverRejected e = noFalseRejection (validate e)

validSourceReviewNeverRejected : ∀ e r → ReviewSourcesValid e r →
  reported (validateReviewSources e r) ≡ []
validSourceReviewNeverRejected e r = noFalseRejection (validateReviewSources e r)
