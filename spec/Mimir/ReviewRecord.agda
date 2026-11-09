{-# OPTIONS --safe #-}
-- Review operation over the same concrete store as record_experience.
module Mimir.ReviewRecord where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_; map; _++_; filterᵇ)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; suc; _≟_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool using (not)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (toList)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
open import Data.Integer using (ℤ; +_; ∣_∣)
import Data.Integer.Properties as Integer
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Mimir.ReviewSchema using (Review)
open import Mimir.LearningCandidates using (Candidate)
import Mimir.Validation as Validation
import Mimir.PosteriorComputation as Posterior
import Mimir.ExperienceSchema as Experience
import Mimir.LearningStore as Store
import Mimir.ExperienceRead as Read
import Mimir.ExperienceRecord as Record
import Mimir.ReviewObservation as Observation
import Mimir.ReviewPreparationPublication as Publication
import Mimir.ReviewNumericalPublication as Numerical
import Mimir.CandidateGraph as Graph
import Mimir.CandidateRegistry as Registry
import Mimir.CandidateReview as Candidates
import Mimir.LearningCandidates as Declarations
import Mimir.ApplicationStore as Application
import Mimir.BeliefEmbedding as Embedding
import Mimir.DocumentStore as Documents
import Data.List.Properties as Lists
import Mimir.RevisionBounds as Bounds

data Failure : Set where
  invalid : Validation.Fault → Failure
  invalidExpected missingExperience incoherentSnapshot : Failure
  numeric : Numerical.NumericFailure → Failure

data Decision : Set where
  rejected : Failure → Decision
  replay : Observation.Snapshot → Decision
  fresh : Store.World → Observation.Snapshot → Bool → Decision

module WithCalculator (calculator : Posterior.Calculator) (posteriorTime : ℤ) where
  module For (before : Store.World) (old : Observation.Snapshot) (requested : Review)
    (expected : ℕ) (clock : Candidate → ℤ) (now : ℤ)
    (unique : Registry.IDs.Unique (map Graph.nodeID (Publication.World.nodes (Store.World.publication before)))) where

    module N = Numerical.For calculator (Store.World.publication before) (Observation.Snapshot.experience old)
      requested clock posteriorTime unique expected (Store.identities before) (Store.World.grounding before)

    convert : N.Decision → Decision
    convert (N.refused failure) = rejected (invalid failure)
    convert (N.numericFailure failure) = rejected (numeric failure)
    convert (N.replay receipt) = replay (record old { candidateIDs = N.P.replayBindings receipt })
    convert d@(N.fresh selected nodes same limit) = fresh
      (record before
        { publication = N.proposed d
        ; current = Store.reviewed (record result { candidateIDs = [] }) (Store.World.current before)
        ; reviewTimes = Store.reviewTime (Review.experienceID requested) (suc expected) now ∷ Store.World.reviewTimes before }) result limit
      where
      result = record old
        { reviewRevision = + suc expected
        ; reviewedRevision = Observation.Snapshot.revision old
        ; candidateIDs = Candidates.Prepared.bindings
            (N.F.P.Prepared.reservation (N.F.Fresh.preparation selected)) }

    plan : (Candidate → ℕ) → Decision
    plan identities = convert (N.plan identities)

  checkState : Store.World → Observation.Snapshot → Review → ℕ → (Candidate → ℤ) → ℤ → (Candidate → ℕ) → Decision
  checkState before old requested expected clock now identities with Observation.checkSnapshot old
  ... | Validation.rejected failure refutation = rejected (invalid failure)
  ... | Validation.accepted valid with Record.coherent before old
  ...   | false = rejected incoherentSnapshot
  ...   | true with Registry.IDs.checkUnique (map Graph.nodeID (Publication.World.nodes (Store.World.publication before)))
  ...     | Validation.rejected failure refutation = rejected (invalid failure)
  ...     | Validation.accepted unique = For.plan before old requested expected clock now unique identities

  plan : Store.World → Review → ℤ → (Candidate → ℤ) → ℤ → (Candidate → ℕ) → Decision
  plan before requested expected clock now identities with does ((+ 0) Integer.≤? expected) ∧ does (expected Integer.<? (+ Bounds.i64Maximum))
  ... | false = rejected invalidExpected
  ... | true with Read.get (Review.experienceID requested) (Store.World.current before)
  ...   | nothing = rejected missingExperience
  ...   | just old = checkState before old requested ∣ expected ∣ clock now identities

proposed : Store.World → Decision → Store.World
proposed before (rejected failure) = before
proposed before (replay receipt) = before
proposed before (fresh after receipt limit) = after

replayPreservesStore : ∀ before receipt → proposed before (replay receipt) ≡ before
replayPreservesStore before receipt = refl

rejectionPreservesStore : ∀ before failure → proposed before (rejected failure) ≡ before
rejectionPreservesStore before failure = refl

-- New-belief preparation is carried into the same complete application world
-- as the review, rather than published as subsequent vector/grounding writes.
-- IDs and times are database observations, never generated by this function.
record PreparedCandidate : Set where
  constructor preparedCandidate
  field key : Text; identity : ℕ; timestamp : ℤ; value : Embedding.Prepared

preparedFor : Text → List PreparedCandidate → Data.Maybe.Maybe PreparedCandidate
preparedFor key [] = nothing
preparedFor key (first ∷ rest) with does (key ≟Text PreparedCandidate.key first)
... | true = just first
... | false = preparedFor key rest

PreparedSelection = List (Graph.BeliefValues × Embedding.Prepared)

selectPrepared : Application.World → ℕ → Text → List Candidate → List PreparedCandidate →
  Data.Maybe.Maybe PreparedSelection
selectPrepared before experience project [] supplied = just []
selectPrepared before experience project (Declarations.patternCandidate _ _ _ ∷ rest) supplied =
  selectPrepared before experience project rest supplied
selectPrepared before experience project (candidate@(Declarations.belief key content memory cited) ∷ rest) supplied
  with Registry.lookup (experience , key)
    (Publication.World.registry (Store.World.publication (Application.World.learning before)))
... | just existing = selectPrepared before experience project rest supplied
... | nothing with preparedFor key supplied
...   | nothing = nothing
...   | just prepared with Graph.value
  (Graph.creation experience (PreparedCandidate.identity prepared) candidate project (PreparedCandidate.timestamp prepared))
...     | Graph.patternNode _ = nothing
...     | Graph.beliefNode belief with Embedding.ownsPreparation belief (Application.World.embeddingOwners before) ∧
  Embedding.usableVector (Embedding.Prepared.vector (PreparedCandidate.value prepared)) ∧
  Embedding.allSupportCurrent belief before (Embedding.supports (PreparedCandidate.value prepared)) ∧
  does (Lists.≡-dec Documents.citationEqual cited (map proj₂ (Embedding.supports (PreparedCandidate.value prepared))))
...       | false = nothing
...       | true with selectPrepared before experience project rest supplied
...         | nothing = nothing
...         | just following = just ((belief , PreparedCandidate.value prepared) ∷ following)

installPrepared : PreparedSelection → Application.World → Application.World
installPrepared [] before = before
installPrepared ((belief , value) ∷ rest) before = installPrepared rest (record before
  { beliefVectors = Application.putVector (Graph.BeliefValues.identity belief) (Embedding.Prepared.vector value)
      (Application.World.beliefVectors before)
  ; beliefSources = (Graph.BeliefValues.identity belief , map proj₂ (Embedding.supports value)) ∷ Application.World.beliefSources before
  ; embeddingOwners = filterᵇ (λ owner → not (does
      (Application.EmbeddingOwnerRow.token owner ≟ Graph.BeliefValues.identity belief)))
      (Application.World.embeddingOwners before) })

module PreparedReview (calculator : Posterior.Calculator) (posteriorTime : ℤ) (requested : Review) (expected : ℤ) (clock : Candidate → ℤ)
  (now : ℤ) (identities : Candidate → ℕ) (supplied : List PreparedCandidate) where

  identity : Candidate → ℕ
  identity candidate with preparedFor (Declarations.candidateKey candidate) supplied
  ... | nothing = identities candidate
  ... | just prepared = PreparedCandidate.identity prepared

  timestamp : Candidate → ℤ
  timestamp candidate with preparedFor (Declarations.candidateKey candidate) supplied
  ... | nothing = clock candidate
  ... | just prepared = PreparedCandidate.timestamp prepared

  selections : Application.World → Data.Maybe.Maybe PreparedSelection
  selections before with Read.get (Review.experienceID requested) (Store.World.current (Application.World.learning before))
  ... | nothing = nothing
  ... | just old = selectPrepared before (Review.experienceID requested)
    (Experience.Experience.project (Observation.Snapshot.experience old)) (Review.candidates requested) supplied

  chosen : Data.Maybe.Maybe PreparedSelection → PreparedSelection
  chosen nothing = []
  chosen (just values) = values

  pending : Application.World → Store.World
  pending before = Application.learningView before

  data Result : Set where
    refused : Failure → Result
    needsPreparation : Result
    replayed : Observation.Snapshot → Result
    published : Application.World → Observation.Snapshot → Bool → Result

  finish : Application.World → Data.Maybe.Maybe PreparedSelection → Decision → Result
  finish before selection (rejected failure) = refused failure
  finish before selection (replay observed) = replayed observed
  finish before nothing (fresh after observed limit) = needsPreparation
  finish before (just values) (fresh after observed limit) = published
    (record preparedState { learning = Application.learningView preparedState }) observed limit
    where preparedState = installPrepared values (Application.installLearning after before)

  intended : Application.World → Result
  intended before = finish before (selections before)
    (WithCalculator.plan calculator posteriorTime (pending before) requested expected timestamp now identity)

  missingPreparationCannotPublish : ∀ before after observed limit →
    finish before nothing (fresh after observed limit) ≡ needsPreparation
  missingPreparationCannotPublish before after observed limit = refl

  missingPreparationRulesOutPublication : ∀ before after observed limit →
    selections before ≡ nothing → intended before ≢ published after observed limit
  missingPreparationRulesOutPublication before after observed limit missing
    with WithCalculator.plan calculator posteriorTime (pending before) requested expected timestamp now identity
  ... | rejected failure = λ ()
  ... | replay original = λ ()
  ... | fresh proposed original numericLimit rewrite missing = λ ()

  replayDoesNotPublish : ∀ before selection observed →
    finish before selection (replay observed) ≡ replayed observed
  replayDoesNotPublish before selection observed = refl
