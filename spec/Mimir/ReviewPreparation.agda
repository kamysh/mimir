{-# OPTIONS --safe #-}
-- Fresh-review preparation after revision classification. Candidate IDs,
-- tentative nodes, concrete materialization and semantic admission share the
-- same inputs. Expected-review revision checks and SQL publication remain
-- separate obligations; this pure plan performs neither database writes nor
-- an assumption that materialization succeeds.
module Mimir.ReviewPreparation where

open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (Maybe)
open import Data.Product using (_,_)
open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ)
open import Data.Sum using (_⊎_; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Mimir.Validation using (Fault; result)
open import Mimir.RecordDecoding using (_>>=_)
open import Mimir.ExperienceSchema using (Experience; validateReviewSources)
open import Mimir.ReviewSchema using (Review; validateReview)
import Mimir.ReviewSchema as Reviews
open import Mimir.LearningCandidates using (Candidate)
import Mimir.CandidateRegistry as Registry
import Mimir.CandidateReview as Candidates
import Mimir.CandidateGraph as Graph
import Mimir.CandidatePublication as Publication
import Mimir.CandidateGraphUniqueness as Uniqueness
import Mimir.ReviewAdmission as Admission
import Mimir.LearningTargets as Targets
import Mimir.ItemOwners as Owners
import Mimir.ItemOwnerBatch as Ownership
import Mimir.LearningSchema as Items
import Mimir.ReviewResolution as Resolution

-- Global/project and working/persistent distinctions are preserved when
-- constructing the target-validation view. Patterns cannot become beliefs.
beliefs : List Graph.Node → List Targets.Belief
beliefs [] = []
beliefs (Graph.beliefNode fields ∷ rest) = Targets.belief
  (Graph.BeliefValues.identity fields) (Graph.BeliefValues.project fields)
  (Graph.BeliefValues.memory fields) ∷ beliefs rest
beliefs (Graph.patternNode fields ∷ rest) = beliefs rest

record Input : Set where
  constructor input
  field
    experience : Experience
    sourceRevision : ℕ
    prior : Maybe Review
    registry : Registry.Registry
    owners : Owners.Registry
    nodes : List Graph.Node
    -- The native graph reader must reject ambiguous duplicate identities.
    uniqueNodes : Registry.IDs.Unique (map Graph.nodeID nodes)

module For (before : Input) (requested : Review) (clock : Candidate → ℤ) where
  current = Input.experience before
  occupied = map Graph.nodeID (Input.nodes before)
  module Nodes = Publication.For (λ _ → Experience.project current) clock

  module Unique = Uniqueness.For (λ _ → Experience.project current) clock

  Reservation = Candidates.Prepared occupied (Input.registry before) requested

  proposedNodes : Reservation → List Graph.Node
  proposedNodes reservation = Nodes.realizeBatch (Candidates.Prepared.reservations reservation) (Input.nodes before)

  environment : Reservation → Admission.Environment
  environment reservation = Admission.environment current (Input.sourceRevision before) (Input.prior before)
    (Candidates.Prepared.bindings reservation) (beliefs (proposedNodes reservation))

  originalEnvironment : Admission.Environment
  originalEnvironment = Admission.environment current (Input.sourceRevision before) (Input.prior before)
    [] (beliefs (Input.nodes before))

  record Prepared : Set where
    constructor prepared
    field
      existingReferences : Targets.ReferencesValid (Experience.project current)
        (beliefs (Input.nodes before)) (Admission.existingReferences requested)
      reservation : Reservation
      admitted : Admission.For.Admitted (environment reservation) requested
      materializedAgrees : Admission.For.materialized (environment reservation) requested
        (Admission.For.Admitted.prepared admitted) ≡ Candidates.materialized reservation
      afterOwners : Owners.Registry
      ownershipPlan : Ownership.Batch (Review.experienceID requested) (Input.owners before)
        (Review.extracted requested) afterOwners

  prepare : (Candidate → ℕ) → Fault ⊎ Prepared
  prepare fresh = result (validateReview requested) >>= λ structure →
    result (Admission.checkPin originalEnvironment requested) >>= λ pinned →
    result (Targets.checkReferences (Experience.project current) (beliefs (Input.nodes before))
      (Admission.existingReferences requested)) >>= λ existingReferences →
    result (validateReviewSources current requested) >>= λ sources →
    result (Admission.checkPrior (Input.prior before) requested) >>= λ retained →
    Ownership.prepare (Review.experienceID requested) (Input.owners before) (Review.extracted requested)
      >>= λ { (afterOwners , ownershipPlan) →
    Candidates.prepareValid occupied (Input.registry before) requested structure fresh >>= λ reservation →
    result (validateReviewSources current (Candidates.materialized reservation)) >>= λ materializedSources →
    result (Targets.validate (Experience.project current) (beliefs (proposedNodes reservation))
      (Admission.targetIDs (Candidates.materialized reservation))) >>= λ targets →
    result (Admission.checkRecordedEvidence current (Candidates.materialized reservation)) >>= λ evidence →
    inj₂ (prepared existingReferences reservation record
      { pinned = pinned
      ; retained = retained
      ; sourcesValid = sources
      ; prepared = Candidates.Prepared.resolution reservation
      ; materializedSourcesValid = materializedSources
      ; targetsValid = targets
      ; recordedEvidence = evidence
      } refl afterOwners ownershipPlan) }

  materialized : Prepared → Review
  materialized preparation = Candidates.materialized (Prepared.reservation preparation)

  targetAdmission : (preparation : Prepared) →
    Targets.Valid (Experience.project current) (beliefs (proposedNodes (Prepared.reservation preparation)))
      (Admission.targetIDs (materialized preparation))
  targetAdmission preparation = subst
    (λ review →
       Targets.Valid (Experience.project current)
       (beliefs (proposedNodes (Prepared.reservation preparation)))
       (Admission.targetIDs review))
    (Prepared.materializedAgrees preparation)
    (Admission.For.Admitted.targetsValid
     (Prepared.admitted preparation))

  priorQuotationsRetained : (preparation : Prepared) →
    Admission.PriorRetained (Input.prior before) requested
  priorQuotationsRetained preparation = Admission.For.Admitted.retained (Prepared.admitted preparation)

  proposedUnique : (reservation : Reservation) → Registry.IDs.Unique (map Graph.nodeID (proposedNodes reservation))
  proposedUnique reservation = Unique.preparedUnique (Input.nodes before)
    (Candidates.Prepared.reservations reservation)
    (Input.uniqueNodes before)

  extractedOwnership : (preparation : Prepared) →
    All (Ownership.Owns (Review.experienceID requested) (Prepared.afterOwners preparation))
      (Review.extracted requested)
  extractedOwnership preparation = Ownership.allOwned (Prepared.ownershipPlan preparation)

  recordedOwnershipPreserved : (preparation : Prepared) →
    All (Ownership.Owns (Experience.identity current) (Input.owners before)) (Experience.items current) →
    All (Ownership.Owns (Experience.identity current) (Prepared.afterOwners preparation)) (Experience.items current)
  recordedOwnershipPreserved preparation previouslyOwned = All.map
    (λ {item} owned →
       Ownership.batchPreserves (Prepared.ownershipPlan preparation)
       (Items.LearningItem.identity item)
       (Ownership.owner (Experience.identity current) item) owned)
    previouslyOwned

  materializedTargetsResolved : (preparation : Prepared) →
    All (λ a → Resolution.Apply.Existing [] [] (Items.Assessment.target a))
      (Review.assessments (materialized preparation))
  materializedTargetsResolved preparation = subst
    (λ review →
       All
       (λ a → Resolution.Apply.Existing [] [] (Items.Assessment.target a))
       (Review.assessments review))
    (Prepared.materializedAgrees preparation)
    (Admission.For.admittedAllTargetsResolved
     (environment (Prepared.reservation preparation)) requested
     (Prepared.admitted preparation))

  materializedValid : (preparation : Prepared) → Reviews.ReviewValid (materialized preparation)
  materializedValid preparation = Candidates.validMaterialized (Prepared.reservation preparation)

  materializedKeysUnique : (preparation : Prepared) →
    Reviews.AssessmentKeys.Unique (map Reviews.assessmentKey (Review.assessments (materialized preparation)))
  materializedKeysUnique preparation with materializedValid preparation
  ... | (_ , _ , _ , _ , _ , _ , unique) = unique
