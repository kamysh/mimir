{-# OPTIONS --safe #-}
-- Candidate materialization consumes checked resolution evidence. It cannot
-- silently skip an unresolved target or truncate a contribution collection.
module Mimir.ReviewResolution where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Product using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.Validation hiding (Feedback; feedback)
open import Mimir.OptionalTraversal using (nothingNotJust)
open import Mimir.LearningSchema using (Target; existing; candidate; Assessment)
open import Mimir.LearningCandidates using (Candidate; TargetValid; validateTarget)
open import Mimir.ReviewSchema using (Review; Feedback; feedback; Link; link;
  CandidateFeedback; CandidateLink; ReviewValid; validateReview)

Registry = List (Text × ℕ)

lookup : Text → Registry → Maybe ℕ
lookup name [] = nothing
lookup name ((other , identity) ∷ rest) with name ≟Text other
... | yes _ = just identity
... | no _ = lookup name rest

Resolution : List Candidate → Registry → Target → ℕ → Set
Resolution cs registry (existing original) identity = original ≡ identity
Resolution cs registry (candidate name) identity =
  TargetValid cs (candidate name) × lookup name registry ≡ just identity

Resolved : List Candidate → Registry → Target → Set
Resolved cs registry target = Σ[ identity ∈ ℕ ] Resolution cs registry target identity

resolve : ∀ cs registry target → Checked (Resolved cs registry target)
resolve cs registry (existing identity) = accepted (identity , refl)
resolve cs registry (candidate name) with validateTarget cs (candidate name)
... | rejected failure invalid = rejected failure (λ { (identity , declared , found) → invalid declared })
... | accepted declared with lookup name registry
...   | just identity = accepted (identity , declared , refl)
...   | nothing = rejected (fault [] missingReference "candidate belief key is unresolved")
  (λ { (identity , declared , present) → nothingNotJust present })

-- Dependent map: there is precisely one proof and output for every input.
mapEvidence : ∀ {A B : Set} {P : A → Set} →
  ((x : A) → P x → B) → (xs : List A) → All P xs → List B
mapEvidence f [] [] = []
mapEvidence f (x ∷ xs) (proof ∷ proofs) = f x proof ∷ mapEvidence f xs proofs

mapEvidenceLength : ∀ {A B : Set} {P : A → Set}
  (f : (x : A) → P x → B) xs proofs → length (mapEvidence f xs proofs) ≡ length xs
mapEvidenceLength f [] [] = refl
mapEvidenceLength f (x ∷ xs) (proof ∷ proofs) = cong suc (mapEvidenceLength f xs proofs)

mapEvidenceAll : ∀ {A B : Set} {P : A → Set} {Q : B → Set}
  (f : (x : A) → P x → B) → (∀ x proof → Q (f x proof)) →
  ∀ xs proofs → All Q (mapEvidence f xs proofs)
mapEvidenceAll f property [] [] = []
mapEvidenceAll f property (x ∷ xs) (proof ∷ proofs) =
  property x proof ∷ mapEvidenceAll f property xs proofs

module Apply (cs : List Candidate) (registry : Registry) where
  AssessmentResolved : Assessment → Set
  AssessmentResolved a = Resolved cs registry (Assessment.target a)

  FeedbackResolved : CandidateFeedback → Set
  FeedbackResolved f = Resolved cs registry (CandidateFeedback.target f)

  LinkResolved : CandidateLink → Set
  LinkResolved l = Resolved cs registry (CandidateLink.from l) × Resolved cs registry (CandidateLink.to l)

  assessment : (a : Assessment) → AssessmentResolved a → Assessment
  assessment a (identity , proof) = record a { target = existing identity }

  feedbackValue : (f : CandidateFeedback) → FeedbackResolved f → Feedback
  feedbackValue f (identity , proof) = feedback identity (CandidateFeedback.verdict f) (CandidateFeedback.weight f)

  linkValue : (l : CandidateLink) → LinkResolved l → Link
  linkValue l ((from , fromProof) , (to , toProof)) = link from to (CandidateLink.relation l) (CandidateLink.weight l)

  Ready : Review → Set
  Ready r = All AssessmentResolved (Review.assessments r) ×
    (All FeedbackResolved (Review.candidateFeedbacks r) × All LinkResolved (Review.candidateLinks r))

  checkReady : ∀ r → Checked (Ready r)
  checkReady r = combine
    (at (key "assessments") (allChecked (λ a → resolve cs registry (Assessment.target a)) (Review.assessments r)))
    (combine (at (key "candidate_feedback") (allChecked (λ f → resolve cs registry (CandidateFeedback.target f)) (Review.candidateFeedbacks r)))
      (at (key "candidate_links") (allChecked (λ l → combine
        (at (key "from") (resolve cs registry (CandidateLink.from l)))
        (at (key "to") (resolve cs registry (CandidateLink.to l)))) (Review.candidateLinks r))))

  apply : (r : Review) → Ready r → Review
  apply r (assessments , feedbacks , links) = record r
    { assessments = mapEvidence assessment (Review.assessments r) assessments
    ; feedbacks = Review.feedbacks r ++ mapEvidence feedbackValue (Review.candidateFeedbacks r) feedbacks
    ; links = Review.links r ++ mapEvidence linkValue (Review.candidateLinks r) links
    ; candidateFeedbacks = []
    ; candidateLinks = []
    }

  Existing : Target → Set
  Existing (existing identity) = ⊤
  Existing (candidate name) = Data.Empty.⊥

  assessmentIsExisting : ∀ a proof → Existing (Assessment.target (assessment a proof))
  assessmentIsExisting a (identity , proof) = tt

  allAssessmentsResolved : ∀ r proof →
    All (λ a → Existing (Assessment.target a)) (Review.assessments (apply r proof))
  allAssessmentsResolved r (assessments , feedbacks , links) =
    mapEvidenceAll assessment assessmentIsExisting (Review.assessments r) assessments

  assessmentCountPreserved : ∀ r proof →
    length (Review.assessments (apply r proof)) ≡ length (Review.assessments r)
  assessmentCountPreserved r (assessments , feedbacks , links) =
    mapEvidenceLength assessment (Review.assessments r) assessments

  feedbackCountPreserved : ∀ r proof → length (Review.feedbacks (apply r proof)) ≡
    length (Review.feedbacks r) + length (Review.candidateFeedbacks r)
  feedbackCountPreserved r (assessments , feedbacks , links) = trans
    (length-++ (Review.feedbacks r))
    (cong (length (Review.feedbacks r) +_) (mapEvidenceLength feedbackValue (Review.candidateFeedbacks r) feedbacks))

  linkCountPreserved : ∀ r proof → length (Review.links (apply r proof)) ≡
    length (Review.links r) + length (Review.candidateLinks r)
  linkCountPreserved r (assessments , feedbacks , links) = trans
    (length-++ (Review.links r))
    (cong (length (Review.links r) +_) (mapEvidenceLength linkValue (Review.candidateLinks r) links))

  originalsPreserved : ∀ r proof →
    Review.extracted (apply r proof) ≡ Review.extracted r ×
    Review.coverage (apply r proof) ≡ Review.coverage r
  originalsPreserved r (assessments , feedbacks , links) = refl , refl

  candidateContributionsCleared : ∀ r proof →
    Review.candidateFeedbacks (apply r proof) ≡ [] × Review.candidateLinks (apply r proof) ≡ []
  candidateContributionsCleared r (assessments , feedbacks , links) = refl , refl

  record Prepared (r : Review) : Set where
    constructor prepared
    field
      candidatesAgree : cs ≡ Review.candidates r
      requestedValid : ReviewValid r
      resolution : Ready r
      appliedValid : ReviewValid (apply r resolution)

  -- Resolved aliases can introduce a self-link, duplicate key or overlap even
  -- when the original structural request is valid. Revalidate before effects.
  prepare : (r : Review) → cs ≡ Review.candidates r → Fault ⊎ Prepared r
  prepare r agreement with validateReview r
  ... | rejected failure invalid = inj₁ failure
  ... | accepted requestValid with checkReady r
  ...   | rejected failure invalid = inj₁ failure
  ...   | accepted resolution with validateReview (apply r resolution)
  ...     | rejected failure invalid = inj₁ failure
  ...     | accepted appliedValid = inj₂ (prepared agreement requestValid resolution appliedValid)

  preparedIsStructurallyValid : ∀ r (p : Prepared r) → ReviewValid (apply r (Prepared.resolution p))
  preparedIsStructurallyValid r p = Prepared.appliedValid p

prepareReview : (r : Review) → (registry : Registry) →
  Fault ⊎ Apply.Prepared (Review.candidates r) registry r
prepareReview r registry = Apply.prepare (Review.candidates r) registry r refl
