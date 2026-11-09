{-# OPTIONS --safe #-}
-- A review changes its own revision, contributions and candidate ownership
-- together with every required belief vector and explicit supporting source.
-- Posterior publication time is the observed writer-lock clock, independently
-- of immutable owner-allocation and review-record creation timestamps.
module Mimir.ReviewPublicationIntent where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.Float.Base using (Float)
open import Data.Integer using (ℤ; +_)
open import Data.List using (List; []; _∷_; _++_; map; filterᵇ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _≟_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; subst)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.ApplicationStore as Store
import Mimir.BeliefEmbedding as Embedding
import Mimir.CandidateGraph as Graph
import Mimir.CandidateRegistry as Registry
import Mimir.CandidateReview as Candidates
import Mimir.ExperienceSchema as Experience
import Mimir.ExperienceSourceIntent as SourceIntent
import Mimir.GroundingRecovery as Grounding
import Mimir.InferenceStorageBinding as Inference
import Mimir.LearningCandidates as Declarations
import Mimir.LearningHistoryWire as History
import Mimir.LearningStore as Learning
import Mimir.PosteriorComputation as Posterior
import Mimir.PublicEncoding as Encoding
import Mimir.ReviewNumericalPublication as Numerical
import Mimir.ReviewObservation as Observation
import Mimir.ReviewPlanning as Planning
import Mimir.ReviewPreparationPublication as Publication
import Mimir.ReviewRecord as ReviewRecord
import Mimir.ReviewSchema as Review
import Mimir.StructuredValue as Wire
import Mimir.Validation as Validation

-- Native ExperienceState extends the original source item map with the
-- review item map. Reusing a local key retains one map entry, rather than
-- emitting duplicate JSON object fields or inventing another item identity.
putItem : Text × ℕ → List (Text × ℕ) → List (Text × ℕ)
putItem pair [] = pair ∷ []
putItem pair (first ∷ rest) with proj₁ pair ≟Text proj₁ first
... | yes _ = pair ∷ rest
... | no _ = first ∷ putItem pair rest

extendItems : List (Text × ℕ) → List (Text × ℕ) → List (Text × ℕ)
extendItems [] existingItems = existingItems
extendItems (first ∷ rest) existingItems = extendItems rest (putItem first existingItems)

-- A registered review can consume only the owners reserved for its own
-- token. Existing published candidate identities require no new owner.
ownedBy : ℕ → ℕ → List Store.EmbeddingOwnerRow → Bool
ownedBy token identity [] = false
ownedBy token identity (entry ∷ rest) with Store.EmbeddingOwnerRow.operationToken entry
... | nothing = ownedBy token identity rest
... | just linked = (does (token ≟ linked) ∧ does (identity ≟ Store.EmbeddingOwnerRow.token entry)) ∨ ownedBy token identity rest

ownedSelection : ℕ → ReviewRecord.PreparedSelection → List Store.EmbeddingOwnerRow → Bool
ownedSelection token [] owners = true
ownedSelection token ((belief , value) ∷ rest) owners =
  ownedBy token (Graph.BeliefValues.identity belief) owners ∧ ownedSelection token rest owners

retainOwner : ℕ → Store.EmbeddingOwnerRow → Bool
retainOwner token entry with Store.EmbeddingOwnerRow.operationToken entry
... | nothing = true
... | just linked = not (does (token ≟ linked))

releaseOwners : ℕ → Store.World → Store.World
releaseOwners token before = record before
  { embeddingOwners = filterᵇ (retainOwner token) (Store.World.embeddingOwners before) }

preparedKeepsJournal : ∀ prepared before →
  Store.World.operations (ReviewRecord.installPrepared prepared before) ≡ Store.World.operations before
preparedKeepsJournal [] before = refl
preparedKeepsJournal ((belief , value) ∷ rest) before = preparedKeepsJournal rest _

module Fresh (database : ℕ) (format : Encoding.Formatting)
  (databaseSum : List Float → Float) (calculator : Posterior.Calculator)
  (before : Store.World) (old : Observation.Snapshot) (requested : Review.Review)
  (expected : ℕ) (clock : Declarations.Candidate → ℤ)
  (unique : Registry.IDs.Unique (map Graph.nodeID
    (Publication.World.nodes (Learning.World.publication (Store.World.learning before)))))
  (reviewCreatedAt publicationTime : ℤ) (token : ℕ) (supplied : List ReviewRecord.PreparedCandidate) where
  module Encode = Encoding.Encode format
  module M = SourceIntent.For database format databaseSum calculator
  module B = Grounding.Business databaseSum calculator
  module N = Inference.NumericalOutcome databaseSum
  module Plan = Planning.For (Learning.World.publication (Store.World.learning before))
    (Observation.Snapshot.experience old) requested clock unique expected
  module F = Plan.F

  result : F.Fresh expected → Observation.Snapshot
  result selected = record old
    { reviewRevision = + suc expected
    ; reviewedRevision = Observation.Snapshot.revision old
    ; candidateIDs = Candidates.Prepared.bindings
        (F.P.Prepared.reservation (F.Fresh.preparation selected)) }

  response : F.Fresh expected → Wire.Value
  response selected = Wire.object
    ((toList "experience" , Encode.experience (Observation.Snapshot.experience old)) ∷
     (toList "revision" , Wire.signed (Observation.Snapshot.revision old)) ∷
     (toList "review_revision" , Wire.signed (+ suc expected)) ∷
     (toList "reviewed_revision" , Wire.signed (Observation.Snapshot.revision old)) ∷
     named "candidate_ids" (Observation.Snapshot.candidateIDs (result selected)) ++
     named "item_ids" (extendItems (SourceIntent.itemIDs (Review.Review.extracted requested))
       (SourceIntent.itemIDs (Experience.Experience.items (Observation.Snapshot.experience old)))))
    where
    named : Data.String.String → List (Text × ℕ) → List (Text × Wire.Value)
    named name [] = []
    named name pairs@(_ ∷ _) = (toList name , Wire.object
      (map (λ { (key , identity) → key , Encode.uuid identity }) pairs)) ∷ []

  required : Maybe ReviewRecord.PreparedSelection
  required with ReviewRecord.selectPrepared before (Review.Review.experienceID requested)
    (Experience.Experience.project (Observation.Snapshot.experience old))
    (Review.Review.candidates requested) supplied
  ... | nothing = nothing
  ... | just values with ownedSelection token values (Store.World.embeddingOwners before)
  ... | false = nothing
  ... | true = just values

  -- This is the independently specified publication, before solving its
  -- complete posterior equations. Historical rows and source revisions are
  -- retained; only this review head and its new immutable version are added.
  intended : F.Fresh expected → ReviewRecord.PreparedSelection → Store.World
  intended selected prepared = releaseOwners token (ReviewRecord.installPrepared prepared (record before
    { learning = record learning
      { publication = F.publish selected
      ; current = Learning.reviewed (record (result selected) { candidateIDs = [] }) (Learning.World.current learning)
      ; reviewTimes = Learning.reviewTime (Review.Review.experienceID requested) (suc expected) reviewCreatedAt ∷
          Learning.World.reviewTimes learning }
    ; history = record history
      { heads = SourceIntent.putHead (SourceIntent.header (result selected)) (History.Database.heads history)
      ; reviewRows = History.row (Review.Review.experienceID requested) (+ suc expected)
          (Observation.Snapshot.revision old) reviewCreatedAt
          (Encode.review (F.P.materialized (F.Fresh.preparation selected))) ∷ History.Database.reviewRows history } }))
    where
    learning = Store.World.learning before
    history = Store.World.history before

  roots : F.Fresh expected → List ℕ
  roots selected = Numerical.oldTargets F.prior ++ Numerical.targets requested ++
    map ReviewRecord.PreparedCandidate.identity supplied

  Outcome = B.Diagnostic ⊎ (Store.World × Wire.Value)

  missingPreparation : B.Diagnostic
  missingPreparation = B.requestFault (Validation.fault
    (Validation.key "review" ∷ Validation.key "candidates" ∷ []) Validation.missingEvidence
    "Every new belief requires its original PostgreSQL owner, a usable complete embedding and unchanged indexed supporting passages. Read the saved review and citations and open a user dialog before changing the request. No review was published.")

  SelectedGoal : F.Fresh expected → ReviewRecord.PreparedSelection → N.Context → Outcome → Set
  SelectedGoal selected prepared numerical (inj₁ diagnostic) = B.Selected.DiagnosticGoal publicationTime numerical diagnostic
  SelectedGoal selected prepared numerical (inj₂ (after , reply)) =
    Σ (List (ℕ × Float)) (λ numericalReply →
      N.Completed publicationTime numerical (intended selected prepared) after numericalReply × reply ≡ response selected)

  Goal : F.Fresh expected → Outcome → Set
  Goal selected outcome with required
  ... | nothing = outcome ≡ inj₁ missingPreparation
  ... | just prepared with M.context (Observation.Snapshot.experience old) (roots selected) (intended selected prepared)
  ... | inj₁ issue = outcome ≡ inj₁ (B.preparation issue)
  ... | inj₂ numerical = SelectedGoal selected prepared numerical outcome

  checked : ∀ selected → Σ Outcome (Goal selected)
  checked selected with required
  ... | nothing = inj₁ missingPreparation , refl
  ... | just prepared with M.context (Observation.Snapshot.experience old) (roots selected) (intended selected prepared)
  ... | inj₁ issue = inj₁ (B.preparation issue) , refl
  ... | inj₂ numerical = convert (B.Selected.checked publicationTime numerical (intended selected prepared))
    where
    convert : Σ B.Outcome (B.Selected.Goal publicationTime numerical (intended selected prepared)) →
      Σ Outcome (SelectedGoal selected prepared numerical)
    convert (inj₁ diagnostic , correct) = inj₁ diagnostic , correct
    convert (inj₂ (after , _) , numericalReply , complete , _) =
      inj₂ (after , response selected) , numericalReply , complete , refl

  intendedKeepsJournal : ∀ selected prepared →
    Store.World.operations (intended selected prepared) ≡ Store.World.operations before
  intendedKeepsJournal selected prepared = preparedKeepsJournal prepared _

  publicationKeepsJournal : ∀ selected after reply → Goal selected (inj₂ (after , reply)) →
    Store.World.operations after ≡ Store.World.operations before
  publicationKeepsJournal selected after reply correct with required
  ... | nothing with correct
  ... | ()
  publicationKeepsJournal selected after reply correct | just prepared
    with M.context (Observation.Snapshot.experience old) (roots selected) (intended selected prepared)
  ... | inj₁ issue with correct
  ... | ()
  publicationKeepsJournal selected after reply correct | just prepared | inj₂ numerical = trans
    (cong Store.World.operations
      (N.completedPreservesOtherStoreComponents publicationTime numerical (intended selected prepared) after (proj₁ correct) (proj₁ (proj₂ correct))))
    (intendedKeepsJournal selected prepared)
