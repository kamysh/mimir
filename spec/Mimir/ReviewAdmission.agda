{-# OPTIONS --safe #-}
-- Semantic admission inside the transaction, after candidate reservation.
-- Wire size, item ownership, registry reservation, revision CAS, and physical
-- publication remain separate obligations and are not hidden Boolean inputs.
module Mimir.ReviewAdmission where

open import Data.List using (List; []; _∷_; map; _++_; concatMap)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Mimir.UUIDGroups using (UUID; _≟UUID_)
open import Data.Integer using (+_)
import Data.Integer.Properties as Integer
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Validation hiding (Feedback; feedback)
open import Mimir.ExperienceSchema using (Experience; HasEvidence; checkHasEvidence;
  ReviewSourcesValid; validateReviewSources)
open import Mimir.ReviewSchema using (Review; Feedback; Link; ReviewValid; validateReview)
open import Mimir.LearningSchema using (Target; existing; candidate; Assessment)
open import Mimir.LearningCorrections using (ReviewCorrection; validateReviewCorrection)
import Mimir.ReviewResolution as Resolution
import Mimir.LearningTargets as Targets
open import Mimir.RecordDecoding using (_>>=_)

assessmentIDs : Assessment → List UUID
assessmentIDs a with Assessment.target a
... | existing identity = identity ∷ []
... | candidate name = []

targetIDs : Review → List UUID
targetIDs r = map Feedback.beliefID (Review.feedbacks r) ++ Review.superseded r ++
  concatMap (λ l → Link.from l ∷ Link.to l ∷ []) (Review.links r) ++
  concatMap assessmentIDs (Review.assessments r)

-- Empty contribution sets need no extra legacy evidence. Typed assessment
-- evidence is checked independently, including unresolved zero-weight cases.
RecordedEvidence : Experience → Review → Set
RecordedEvidence e r with Review.feedbacks r | Review.links r | Review.superseded r | Review.candidates r
... | [] | [] | [] | [] = ⊤
... | _ ∷ _ | _ | _ | _ = HasEvidence (Experience.evidence e)
... | [] | _ ∷ _ | _ | _ = HasEvidence (Experience.evidence e)
... | [] | [] | _ ∷ _ | _ = HasEvidence (Experience.evidence e)
... | [] | [] | [] | _ ∷ _ = HasEvidence (Experience.evidence e)

checkRecordedEvidence : ∀ e r → Checked (RecordedEvidence e r)
checkRecordedEvidence e r with Review.feedbacks r | Review.links r | Review.superseded r | Review.candidates r
... | [] | [] | [] | [] = accepted tt
... | _ ∷ _ | _ | _ | _ = checkHasEvidence (Experience.evidence e)
... | [] | _ ∷ _ | _ | _ = checkHasEvidence (Experience.evidence e)
... | [] | [] | _ ∷ _ | _ = checkHasEvidence (Experience.evidence e)
... | [] | [] | [] | _ ∷ _ = checkHasEvidence (Experience.evidence e)

PriorRetained : Maybe Review → Review → Set
PriorRetained nothing requested = ⊤
PriorRetained (just prior) requested = ReviewCorrection prior requested

checkPrior : ∀ prior requested → Checked (PriorRetained prior requested)
checkPrior nothing requested = accepted tt
checkPrior (just prior) requested = validateReviewCorrection prior requested

record Environment : Set where
  constructor environment
  field
    experience : Experience
    sourceRevision : ℕ
    prior : Maybe Review
    registry : Resolution.Registry
    beliefs : List Targets.Belief

Pinned : Environment → Review → Set
Pinned env requested = Review.experienceID requested ≡ Experience.identity (Environment.experience env) ×
  Review.experienceRevision requested ≡ (+ Environment.sourceRevision env)

checkPin : ∀ env requested → Checked (Pinned env requested)
checkPin env requested = combine
  (check (fault [] wrongIdentity "review belongs to another experience")
    (Review.experienceID requested ≟UUID Experience.identity (Environment.experience env)))
  (check (fault [] staleRevision "experience has changed")
    (Review.experienceRevision requested Integer.≟ (+ Environment.sourceRevision env)))

module For (env : Environment) (requested : Review) where
  module Apply = Resolution.Apply (Review.candidates requested) (Environment.registry env)

  materialized : Apply.Prepared requested → Review
  materialized p = Apply.apply requested (Apply.Prepared.resolution p)

  record Admitted : Set where
    constructor admitted
    field
      pinned : Pinned env requested
      retained : PriorRetained (Environment.prior env) requested
      sourcesValid : ReviewSourcesValid (Environment.experience env) requested
      prepared : Apply.Prepared requested
      materializedSourcesValid : ReviewSourcesValid (Environment.experience env) (materialized prepared)
      targetsValid : Targets.Valid (Experience.project (Environment.experience env))
        (Environment.beliefs env) (targetIDs (materialized prepared))
      recordedEvidence : RecordedEvidence (Environment.experience env) (materialized prepared)

  admit : Fault ⊎ Admitted
  admit = result (validateReview requested) >>= λ structurallyValid →
    result (checkPin env requested) >>= λ pinned →
    result (validateReviewSources (Environment.experience env) requested) >>= λ sourcesValid →
    result (checkPrior (Environment.prior env) requested) >>= λ retained →
    Resolution.prepareReview requested (Environment.registry env) >>= λ prepared →
    result (validateReviewSources (Environment.experience env) (materialized prepared)) >>= λ materializedSourcesValid →
    result (Targets.validate (Experience.project (Environment.experience env))
      (Environment.beliefs env) (targetIDs (materialized prepared))) >>= λ targetsValid →
    result (checkRecordedEvidence (Environment.experience env) (materialized prepared)) >>= λ evidence →
    inj₂ (admitted pinned retained sourcesValid prepared materializedSourcesValid targetsValid evidence)

  admittedRequestValid : Admitted → ReviewValid requested
  admittedRequestValid a = Apply.Prepared.requestedValid (Admitted.prepared a)

  admittedAppliedValid : (a : Admitted) → ReviewValid (materialized (Admitted.prepared a))
  admittedAppliedValid a = Apply.Prepared.appliedValid (Admitted.prepared a)

  admittedAssessmentCount : (a : Admitted) →
    Data.List.length (Review.assessments (materialized (Admitted.prepared a))) ≡
    Data.List.length (Review.assessments requested)
  admittedAssessmentCount a = Apply.assessmentCountPreserved requested
    (Apply.Prepared.resolution (Admitted.prepared a))

  admittedAllTargetsResolved : (a : Admitted) →
    All (λ assessment → Apply.Existing (Assessment.target assessment))
      (Review.assessments (materialized (Admitted.prepared a)))
  admittedAllTargetsResolved a = Apply.allAssessmentsResolved requested
    (Apply.Prepared.resolution (Admitted.prepared a))
