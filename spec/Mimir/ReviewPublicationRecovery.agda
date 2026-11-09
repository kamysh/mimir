{-# OPTIONS --safe #-}
-- A registered review derives its publication from the original request,
-- observed preparation packets and PostgreSQL allocation/clock receipts.
-- FinalBody certifies the final transaction only. The independently committed
-- owner prefix, provider ownership and initial saved-prefix admission must be
-- composed before this can be dispatched as the whole review operation.
module Mimir.ReviewPublicationRecovery where

open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Float.Base using (Float)
open import Data.Integer using (ℤ; ∣_∣; +_)
import Data.Integer.Properties as Integer
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Properties as Maybes
open import Data.Nat using (ℕ; suc; zero; _≟_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String using (toList; fromList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; subst)
open import Relation.Binary.PropositionalEquality using (sym)
open import Relation.Nullary using (yes; no; does)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.ApplicationStore as Store
import Mimir.CandidateGraph as Graph
import Mimir.CandidateRegistry as Registry
import Mimir.ExperienceRead as Read
import Mimir.ExperienceRecord as Recording
import Mimir.ExperienceSourceIntent as Source
import Mimir.GroundingRecovery as Grounding
import Mimir.IndependentBeliefRecovery as Independent
import Mimir.LearningCandidates as Candidates
import Mimir.LearningInput as Input
import Mimir.LearningOperations as Operations
import Mimir.LearningKeys as Keys
import Mimir.LearningSchema as Items
import Mimir.LearningStore as Learning
import Mimir.PosteriorComputation as Posterior
import Mimir.OperationControls as Controls
import Mimir.PublicEncoding as Encoding
import Mimir.ReviewObservation as Observation
import Mimir.ReviewPlanning as Planning
import Mimir.ReviewLedger as Ledger
import Mimir.ReviewPreparationPublication as Publication
import Mimir.ReviewPublicationIntent as Intent
import Mimir.ReviewRecord as Record
import Mimir.ReviewSchema as Review
import Mimir.StructuredValue as Wire
import Mimir.Validation as Validation
import Mimir.RecoverableStoreStep as Step
import Mimir.RegisteredStoreAdmission as Admission
import Mimir.StandardLibrary as Library
import Mimir.PublicRequest as Public
import Mimir.ToolCatalog as Tools
import Mimir.Recovery as Recovery
import Mimir.DatabaseTransaction as DB
import Mimir.EmbeddingLifecycle as Lifecycle
import Mimir.BeliefEmbedding as Embedding
import Mimir.ExperienceSchema as Experience

record Request : Set where
  constructor request
  field original : Input.Review; expected : ℤ

-- Shared state-dependent preparation checks. These allocate no item, owner or
-- graph identity. Raw field/schema admission remains at the calling boundary.
module PreparationStatus where
  data Status : Set where
    blocked : Validation.Fault → Status
    alreadyApplied : Observation.Snapshot → Status
    waiting : Observation.Snapshot → List (ℕ × Candidates.Candidate) → Status

  currentCandidates : ℕ → Registry.Registry → ℕ → List Candidates.Candidate →
    Validation.Fault ⊎ List (ℕ × Candidates.Candidate)
  currentCandidates experience registry index [] = inj₂ []
  currentCandidates experience registry index (candidate ∷ rest)
    with Registry.lookup (experience , Candidates.candidateKey candidate) registry
  ... | nothing with currentCandidates experience registry (suc index) rest
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ remaining = inj₂ ((index , candidate) ∷ remaining)
  currentCandidates experience registry index (candidate ∷ rest) | just stored
    with Registry.checkExisting candidate stored
  ... | Validation.rejected fault _ = inj₁ (Validation.prependPath (Validation.key "review")
    (Validation.prependPath (Validation.key "candidates") (Validation.prependPath (Validation.index index) fault)))
  ... | Validation.accepted _ = currentCandidates experience registry (suc index) rest

  sourceFault reviewFault : Validation.Fault
  sourceFault = Validation.fault (Validation.key "review" ∷ Validation.key "experience_revision" ∷ []) Validation.staleRevision
    "The original experience source revision changed. Stop this preparation, read the current source and original review, and open the user dialog before choosing corrected work."
  reviewFault = Validation.fault (Validation.key "expected_review_revision" ∷ []) Validation.staleRevision
    "Another review changed the expected review revision. Stop this preparation, read the current review and original saved operation, and open the user dialog; do not overwrite it."

  atSnapshot : Request → Store.World → Observation.Snapshot → Status
  atSnapshot input before old with Input.Review.experienceRevision (Request.original input) Integer.≟ Observation.Snapshot.revision old
  ... | Relation.Nullary.no _ = blocked sourceFault
  ... | Relation.Nullary.yes _ with Ledger.R.replay
    (Ledger.World.cells (Publication.World.ledger (Learning.World.publication (Store.World.learning before)))
      (Input.Review.experienceID (Request.original input))) ∣ Request.expected input ∣ (Keys.reviewInput (Request.original input))
  ... | true = alreadyApplied old
  ... | false with Request.expected input Integer.≟ Observation.Snapshot.reviewRevision old
  ... | Relation.Nullary.no _ = blocked reviewFault
  ... | Relation.Nullary.yes _ with currentCandidates (Input.Review.experienceID (Request.original input))
    (Publication.World.registry (Learning.World.publication (Store.World.learning before))) 0
    (Input.Review.candidates (Request.original input))
  ... | inj₁ fault = blocked fault
  ... | inj₂ selected = waiting old selected

  inspect : Request → Store.World → Status
  inspect input before with Operations.expectedValid (Request.expected input)
  ... | false = blocked (Validation.fault (Validation.key "expected_review_revision" ∷ []) Validation.invalidNumber
    "Read the original current review revision; it must be nonnegative and leave one representable increment. Do not clamp or invent a revision.")
  ... | true with Read.get (Input.Review.experienceID (Request.original input)) (Learning.World.current (Store.World.learning before))
  ... | nothing = blocked (Validation.fault (Validation.key "review" ∷ Validation.key "experience_id" ∷ []) Validation.missingReference
    "The original experience no longer exists. Stop this preparation and open the user dialog after reading the original operation; do not recreate a deleted incident.")
  ... | just old with Observation.checkSnapshot old
  ... | Validation.rejected fault _ = blocked fault
  ... | Validation.accepted _ with Recording.coherent (Store.World.learning before) old
  ... | false = blocked (Validation.fault [] Validation.malformedInput
    "The current source and review header disagree. Stop preparation and read its source, history and diagnostics before continuing.")
  ... | true = atSnapshot input before old

  changedSourceRefuses : ∀ input before old →
    Input.Review.experienceRevision (Request.original input) Relation.Binary.PropositionalEquality.≢ Observation.Snapshot.revision old →
    atSnapshot input before old ≡ blocked sourceFault
  changedSourceRefuses input before old different
    with Input.Review.experienceRevision (Request.original input) Integer.≟ Observation.Snapshot.revision old
  ... | no _ = refl
  ... | yes same = ⊥-elim (different same)

  checkedOwnership : Request → Store.World → Lifecycle.Ownership.State → Lifecycle.Ownership.State
  checkedOwnership input before owned with inspect input before
  ... | blocked _ = Lifecycle.Ownership.stop owned
  ... | alreadyApplied _ = Lifecycle.Ownership.stop owned
  ... | waiting _ _ = owned

  refusedPreparationStopsItsJob : ∀ input before fault owned → inspect input before ≡ blocked fault →
    checkedOwnership input before owned ≡ Lifecycle.Ownership.stop owned
  refusedPreparationStopsItsJob input before fault owned observed rewrite observed = refl

  completedReviewStopsRedundantJob : ∀ input before old owned → inspect input before ≡ alreadyApplied old →
    checkedOwnership input before owned ≡ Lifecycle.Ownership.stop owned
  completedReviewStopsRedundantJob input before old owned observed rewrite observed = refl

-- A provider packet is tied to the original declaration, its saved PG owner
-- and the actual indexed passages. The vector itself remains an external
-- response; it is never an expected vector in the operation input.
module Preparing where
  Allocations = List (Text × Store.EmbeddingOwnerRow)

  allocation : Text → Allocations → Maybe Store.EmbeddingOwnerRow
  allocation key [] = nothing
  allocation key ((name , row) ∷ rest) with key ≟Text name
  ... | yes _ = just row
  ... | no _ = allocation key rest

  candidateAt : ℕ → List Candidates.Candidate → Maybe Candidates.Candidate
  candidateAt zero [] = nothing
  candidateAt zero (first ∷ _) = just first
  candidateAt (suc index) [] = nothing
  candidateAt (suc index) (_ ∷ rest) = candidateAt index rest

  sameOwner : Store.EmbeddingOwnerRow → Store.EmbeddingOwnerRow → Bool
  sameOwner saved actual =
    does (Store.EmbeddingOwnerRow.token saved ≟ Store.EmbeddingOwnerRow.token actual) ∧
    does (Store.EmbeddingOwnerRow.reservedAt saved Integer.≟ Store.EmbeddingOwnerRow.reservedAt actual) ∧
    does (Maybes.≡-dec _≟Text_ (Store.EmbeddingOwnerRow.project saved) (Store.EmbeddingOwnerRow.project actual)) ∧
    does (Maybes.≡-dec _≟_ (Store.EmbeddingOwnerRow.operationToken saved) (Store.EmbeddingOwnerRow.operationToken actual))

  ownerPresent : Store.EmbeddingOwnerRow → List Store.EmbeddingOwnerRow → Bool
  ownerPresent saved [] = false
  ownerPresent saved (first ∷ rest) = sameOwner saved first ∨ ownerPresent saved rest

  record Claim : Set where
    constructor claim
    field
      index : ℕ
      key : Text
      owner : Store.EmbeddingOwnerRow
      belief : Graph.BeliefValues
      firstSupport : Embedding.Support
      remainingSupport : List Embedding.Support

  supports : Claim → List Embedding.Support
  supports selected = Claim.firstSupport selected ∷ Claim.remainingSupport selected

  unavailable : Validation.Fault
  unavailable = Validation.fault (Validation.key "review" ∷ Validation.key "candidates" ∷ []) Validation.missingReference
    "The original candidate or its saved PostgreSQL owner is unavailable. Stop this job, read its original plan and answers, and open the user dialog; do not allocate a replacement identity or recreate deleted work. No review was published."

  makeClaim : ℕ → Request → Allocations → ℕ → Store.World → Validation.Fault ⊎ Claim
  makeClaim token input allocations index before
    with candidateAt index (Input.Review.candidates (Request.original input))
       | Read.get (Input.Review.experienceID (Request.original input)) (Learning.World.current (Store.World.learning before))
  ... | nothing | _ = inj₁ unavailable
  ... | just (Candidates.patternCandidate _ _ _) | _ = inj₁ unavailable
  ... | _ | nothing = inj₁ unavailable
  ... | just candidate@(Candidates.belief key content memory cited) | just old with allocation key allocations
  ... | nothing = inj₁ unavailable
  ... | just saved with ownerPresent saved (Store.World.embeddingOwners before) ∧
    does (Maybes.≡-dec _≟_ (Store.EmbeddingOwnerRow.operationToken saved) (just token)) ∧
    does (Maybes.≡-dec _≟Text_ (Store.EmbeddingOwnerRow.project saved)
      (just (Experience.Experience.project (Observation.Snapshot.experience old))))
  ... | false = inj₁ unavailable
  ... | true with Graph.value (Graph.creation (Input.Review.experienceID (Request.original input))
    (Store.EmbeddingOwnerRow.token saved) candidate
    (Experience.Experience.project (Observation.Snapshot.experience old)) (Store.EmbeddingOwnerRow.reservedAt saved))
  ... | Graph.patternNode _ = inj₁ unavailable
  ... | Graph.beliefNode belief with Embedding.validateCitations belief before cited
  ... | Validation.rejected fault _ = inj₁ fault
  ... | Validation.accepted _ with Embedding.selectSupport belief before cited
  ... | inj₁ cause = inj₁ (Validation.fault (Validation.key "review" ∷ Validation.key "candidates" ∷ Validation.index index ∷ [])
    Validation.missingEvidence (fromList cause))
  ... | inj₂ [] = inj₁ unavailable
  ... | inj₂ (first ∷ rest) = inj₂ (claim index key saved belief first rest)

  current : ℕ → Request → Allocations → Claim → Store.World → Bool
  current token input allocations selected before with PreparationStatus.inspect input before
  ... | PreparationStatus.blocked _ = false
  ... | PreparationStatus.alreadyApplied _ = false
  ... | PreparationStatus.waiting _ _ =
    ownerPresent (Claim.owner selected) (Store.World.embeddingOwners before) ∧
    Embedding.preparationCurrent (Claim.belief selected) (supports selected) before

  checkedOwnership : ℕ → Request → Allocations → Claim → Store.World →
    Lifecycle.Ownership.State → Lifecycle.Ownership.State
  checkedOwnership token input allocations selected before owned with current token input allocations selected before
  ... | false = Lifecycle.Ownership.stop owned
  ... | true = owned

  revokedClaimStopsItsJob : ∀ token input allocations selected before owned →
    current token input allocations selected before ≡ false →
    checkedOwnership token input allocations selected before owned ≡ Lifecycle.Ownership.stop owned
  revokedClaimStopsItsJob token input allocations selected before owned noLongerCurrent rewrite noLongerCurrent = refl

  observe : Claim → Text ⊎ List Store.Vector → Validation.Fault ⊎ Record.PreparedCandidate
  observe selected (inj₁ cause) = inj₁ (Validation.fault (Validation.key "embeddings" ∷ []) Validation.missingEvidence (fromList cause))
  observe selected (inj₂ (vector ∷ [])) with Embedding.usableVector vector
  ... | false = inj₁ (Validation.fault (Validation.key "embeddings" ∷ []) Validation.missingEvidence
    "The backend returned an unusable vector. Open the user dialog to repair the backend; no review was published.")
  ... | true = inj₂ (Record.preparedCandidate (Claim.key selected)
    (Graph.BeliefValues.identity (Claim.belief selected)) (Graph.BeliefValues.created (Claim.belief selected))
    (Embedding.prepared vector (Claim.firstSupport selected) (Claim.remainingSupport selected)))
  observe selected (inj₂ _) = inj₁ (Validation.fault (Validation.key "embeddings" ∷ []) Validation.missingEvidence
    "The backend must return exactly one complete vector for this candidate. Open the user dialog; no review was published.")

  successfulPacketHasOriginalInput : ∀ selected raw packet → observe selected raw ≡ inj₂ packet →
    Record.PreparedCandidate.key packet ≡ Claim.key selected ×
    Record.PreparedCandidate.identity packet ≡ Graph.BeliefValues.identity (Claim.belief selected) ×
    Record.PreparedCandidate.timestamp packet ≡ Graph.BeliefValues.created (Claim.belief selected) ×
    Σ Store.Vector (λ vector → raw ≡ inj₂ (vector ∷ []) × Embedding.usableVector vector ≡ true ×
      Embedding.Prepared.vector (Record.PreparedCandidate.value packet) ≡ vector ×
      Embedding.supports (Record.PreparedCandidate.value packet) ≡ supports selected)
  successfulPacketHasOriginalInput selected (inj₁ _) packet ()
  successfulPacketHasOriginalInput selected (inj₂ []) packet ()
  successfulPacketHasOriginalInput selected (inj₂ (_ ∷ _ ∷ _)) packet ()
  successfulPacketHasOriginalInput selected (inj₂ (vector ∷ [])) packet accepted
    with Embedding.usableVector vector in usable
  ... | false with accepted
  ... | ()
  successfulPacketHasOriginalInput selected (inj₂ (vector ∷ [])) packet accepted | true with accepted
  ... | refl = refl , refl , refl , vector , refl , usable , refl , refl

-- Every field is a physical execution observation. It is not a tool argument
-- or a desired result supplied by the caller. Saved owners determine belief
-- identities/times; pattern and item allocation occurs in the final TX.
record Metadata : Set where
  field
    identities : Candidates.Candidate → ℕ
    creationTimes : Candidates.Candidate → ℤ
    reviewCreatedAt publicationTime : ℤ
    itemReplies : List (Operations.Failure ⊎ ℕ)
    prepared : List Record.PreparedCandidate

  -- New beliefs use their prepared owner's allocation. The final transaction
  -- allocates only pattern identities; no independent ID can be paired with
  -- a vector that belongs to a different prepared belief.
  identity : Candidates.Candidate → ℕ
  identity candidate@(Candidates.patternCandidate _ _ _) = identities candidate
  identity candidate@(Candidates.belief _ _ _ _) with Record.preparedFor (Candidates.candidateKey candidate) prepared
  ... | just value = Record.PreparedCandidate.identity value
  ... | nothing = identities candidate

  creationTime : Candidates.Candidate → ℤ
  creationTime candidate@(Candidates.patternCandidate _ _ _) = creationTimes candidate
  creationTime candidate@(Candidates.belief _ _ _ _) with Record.preparedFor (Candidates.candidateKey candidate) prepared
  ... | just value = Record.PreparedCandidate.timestamp value
  ... | nothing = creationTimes candidate

module Business (database : ℕ) (format : Encoding.Formatting)
  (databaseSum : List Float → Float) (calculator : Posterior.Calculator) where
  module M = Source.For database format databaseSum calculator
  module B = Grounding.Business databaseSum calculator
  Diagnostic = Validation.Fault ⊎ (Operations.Failure ⊎ B.Diagnostic)
  Outcome = Diagnostic ⊎ (Store.World × Wire.Value)

  malformed : Data.String.String → Validation.Fault
  malformed detail = Validation.fault [] Validation.malformedInput detail

  missingObservation = malformed "The actual item-allocation observation is incomplete. Read the original token and diagnostics; do not invent an item ID or repeat a possibly committed review."

  Context : Store.World → Set
  Context before = Observation.Snapshot × Registry.IDs.Unique
    (map Graph.nodeID (Publication.World.nodes (Learning.World.publication (Store.World.learning before))))

  inspect : (before : Store.World) → Input.Review → Validation.Fault ⊎ Context before
  inspect before input with Read.get (Input.Review.experienceID input) (Learning.World.current (Store.World.learning before))
  ... | nothing = inj₁ (Validation.fault (Validation.key "review" ∷ Validation.key "experience_id" ∷ []) Validation.missingReference
    "The experience is not stored. Read the original review and experience ID; open the user dialog rather than creating a replacement incident.")
  ... | just old with Observation.checkSnapshot old
  ... | Validation.rejected fault _ = inj₁ fault
  ... | Validation.accepted _ with Recording.coherent (Store.World.learning before) old
  ... | false = inj₁ (malformed "The stored source and review header disagree. Read the original experience and history before resuming; no review was published.")
  ... | true with Registry.IDs.checkUnique
    (map Graph.nodeID (Publication.World.nodes (Learning.World.publication (Store.World.learning before))))
  ... | Validation.rejected fault _ = inj₁ fault
  ... | Validation.accepted unique = inj₂ (old , unique)

  module Selected (token : ℕ) (initial : Store.World) (staged : Learning.World) (input : Request) (metadata : Metadata)
    (old : Observation.Snapshot)
    (unique : Registry.IDs.Unique
      (map Graph.nodeID (Publication.World.nodes (Learning.World.publication staged))) )
    (canonical : Review.Review) where
    before = record initial { learning = staged }
    module Plan = Planning.WithOriginal (just (Request.original input))
      (Learning.World.publication (Store.World.learning before)) (Observation.Snapshot.experience old)
      canonical (Metadata.creationTime metadata) unique ∣ Request.expected input ∣
    module Fresh = Intent.Fresh database format databaseSum calculator (Request.original input)
      before old canonical ∣ Request.expected input ∣ (Metadata.creationTime metadata) unique
      (Metadata.reviewCreatedAt metadata) (Metadata.publicationTime metadata) token (Metadata.prepared metadata)

    extra : List Items.LearningItem
    extra with Plan.F.prior
    ... | nothing = []
    ... | just prior = Review.Review.extracted prior

    replayReply : Plan.Replayed → Wire.Value
    replayReply replay = Intent.stateReply format
      (record old { candidateIDs = Plan.replayBindings replay }) extra

    Goal : Plan.Decision → Outcome → Set
    Goal (Plan.refused fault) outcome = outcome ≡ inj₁ (inj₁ fault)
    Goal (Plan.replay replay) outcome = outcome ≡ inj₂ (Intent.releaseOwners token initial , replayReply replay)
    Goal (Plan.fresh selected) (inj₁ (inj₂ (inj₂ diagnostic))) = Fresh.Goal selected (inj₁ diagnostic)
    Goal (Plan.fresh selected) (inj₁ _) = ⊥
    Goal (Plan.fresh selected) (inj₂ published) = Fresh.Goal selected (inj₂ published)

    checked : ∀ decision → Σ Outcome (Goal decision)
    checked (Plan.refused fault) = inj₁ (inj₁ fault) , refl
    checked (Plan.replay replay) = inj₂ (Intent.releaseOwners token initial , replayReply replay) , refl
    checked (Plan.fresh selected) = convert (Fresh.checked selected)
      where
      convert : Σ Fresh.Outcome (Fresh.Goal selected) → Σ Outcome (Goal (Plan.fresh selected))
      convert (inj₁ diagnostic , correct) = inj₁ (inj₂ (inj₂ diagnostic)) , correct
      convert (inj₂ published , correct) = inj₂ published , correct

    keepsJournal : ∀ decision after reply → Goal decision (inj₂ (after , reply)) →
      Store.World.operations after ≡ Store.World.operations before
    keepsJournal (Plan.refused _) after reply ()
    keepsJournal (Plan.replay replay) .(Intent.releaseOwners token initial) .(replayReply replay) refl = refl
    keepsJournal (Plan.fresh selected) after reply correct = Fresh.publicationKeepsJournal selected after reply correct

  normalized : Request → Metadata → Store.World → Maybe (Operations.Failure ⊎ (Learning.World × Review.Review))
  normalized input metadata before = M.observe
    (M.Normalize.review (Request.original input) (Store.learningView before)) (Metadata.itemReplies metadata)

  NormalizedGoal : ∀ token input metadata before →
    Maybe (Operations.Failure ⊎ (Learning.World × Review.Review)) → Outcome → Set
  NormalizedGoal token input metadata before nothing outcome = outcome ≡ inj₁ (inj₁ missingObservation)
  NormalizedGoal token input metadata before (just (inj₁ fault)) outcome = outcome ≡ inj₁ (inj₂ (inj₁ fault))
  NormalizedGoal token input metadata before (just (inj₂ (staged , canonical))) outcome
    with inspect (record before { learning = staged }) (Request.original input)
  ... | inj₁ fault = outcome ≡ inj₁ (inj₁ fault)
  ... | inj₂ (old , unique) = Selected.Goal token before staged input metadata old unique canonical
    (Selected.Plan.plan token before staged input metadata old unique canonical (Metadata.identity metadata)) outcome

  normalizedChecked : ∀ token input metadata before current → Σ Outcome (NormalizedGoal token input metadata before current)
  normalizedChecked token input metadata before nothing = inj₁ (inj₁ missingObservation) , refl
  normalizedChecked token input metadata before (just (inj₁ fault)) = inj₁ (inj₂ (inj₁ fault)) , refl
  normalizedChecked token input metadata before (just (inj₂ (staged , canonical)))
    with inspect (record before { learning = staged }) (Request.original input)
  ... | inj₁ fault = inj₁ (inj₁ fault) , refl
  ... | inj₂ (old , unique) = Selected.checked token before staged input metadata old unique canonical
    (Selected.Plan.plan token before staged input metadata old unique canonical (Metadata.identity metadata))

  Goal : ℕ → Request → Metadata → Store.World → Outcome → Set
  Goal token input metadata before outcome with Operations.expectedValid (Request.expected input)
  ... | false = outcome ≡ inj₁ (inj₁ (Validation.fault (Validation.key "expected_review_revision" ∷ []) Validation.invalidNumber
    "Use the original nonnegative review revision with one representable increment; read the current review before changing a request."))
  ... | true = NormalizedGoal token input metadata before (normalized input metadata before) outcome

  checked : ∀ token input metadata before → Σ Outcome (Goal token input metadata before)
  checked token input metadata before with Operations.expectedValid (Request.expected input)
  ... | false = inj₁ (inj₁ (Validation.fault (Validation.key "expected_review_revision" ∷ []) Validation.invalidNumber
    "Use the original nonnegative review revision with one representable increment; read the current review before changing a request.")) , refl
  ... | true = normalizedChecked token input metadata before (normalized input metadata before)

  normalizedKeepsJournal : ∀ token input metadata before current after reply →
    NormalizedGoal token input metadata before current (inj₂ (after , reply)) →
    Store.World.operations after ≡ Store.World.operations before
  normalizedKeepsJournal token input metadata before nothing after reply ()
  normalizedKeepsJournal token input metadata before (just (inj₁ _)) after reply ()
  normalizedKeepsJournal token input metadata before (just (inj₂ (staged , canonical))) after reply correct
    with inspect (record before { learning = staged }) (Request.original input)
  ... | inj₁ _ with correct
  ... | ()
  normalizedKeepsJournal token input metadata before (just (inj₂ (staged , canonical))) after reply correct | inj₂ (old , unique) =
    Selected.keepsJournal token before staged input metadata old unique canonical
      (Selected.Plan.plan token before staged input metadata old unique canonical (Metadata.identity metadata)) after reply correct

  keepsJournal : ∀ token input metadata before after reply → Goal token input metadata before (inj₂ (after , reply)) →
    Store.World.operations after ≡ Store.World.operations before
  keepsJournal token input metadata before after reply correct with Operations.expectedValid (Request.expected input)
  ... | false with correct
  ... | ()
  keepsJournal token input metadata before after reply correct | true =
    normalizedKeepsJournal token input metadata before (normalized input metadata before) after reply correct

  checkedKeepsJournal : ∀ token input metadata before after reply →
    proj₁ (checked token input metadata before) ≡ inj₂ (after , reply) →
    Store.World.operations after ≡ Store.World.operations before
  checkedKeepsJournal token input metadata before after reply observed =
    keepsJournal token input metadata before after reply
      (subst (Goal token input metadata before) observed (proj₂ (checked token input metadata before)))

-- Only a finite progress witness uses this external adapter. Physical reply
-- semantics below accept every actual observation, including another valid
-- provider packet on retry; no deterministic-provider equation is assumed.
record Dependencies : Set where
  field observation : ℕ → Store.World → Metadata

module FinalBody (library : Library.Contract) (format : Encoding.Formatting) (database : ℕ)
  (databaseSum : List Float → Float) (calculator : Posterior.Calculator) (dependencies : Dependencies) where
  module B = Business database format databaseSum calculator
  module D = Public.Decode library
  module Plan = Controls.Plan

  key : ℕ → Text
  key _ = toList "[\"store.review_experience_prepared\",null]"

  distinct : ∀ token → key token ≡ Step.resultKey → ⊥
  distinct token ()

  ownerSteps : List Candidates.Candidate → List Plan.Step
  ownerSteps [] = []
  ownerSteps (Candidates.patternCandidate _ _ _ ∷ rest) = ownerSteps rest
  ownerSteps (Candidates.belief candidateKey _ _ _ ∷ rest) =
    Plan.canonicalStep library (toList "store.reserve_belief_preparation") (just candidateKey) ∷ ownerSteps rest

  expectedSteps : Request → List Plan.Step
  expectedSteps input = Data.List._++_ (ownerSteps (Input.Review.candidates (Request.original input)))
    (Plan.step (toList "store.review_experience_prepared") nothing (key 0) ∷ [])

  mismatch = Validation.fault (Validation.key "plan" ∷ []) Validation.wrongIdentity
    "Read the original review plan, its candidate declarations and server-selected embedding model. Reserve each declared belief key in original order, then publish the review once. Do not replace the token or invent preparation identities."

  arguments : Wire.Value → Validation.Fault ⊎ Request
  arguments raw with D.readTool Tools.reviewExperience raw
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ (Public.learning (Operations.reviewExperience input expected)) = inj₂ (request input expected)
  ... | inj₂ _ = inj₁ mismatch

  original : ℕ → Step.Registration → Validation.Fault ⊎ (Request × ℤ)
  original token registration with Admission.originalPlan (toList "review_experience") token registration
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ (reserved , binding , raw) with Plan.decode raw
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ storedPlan with Plan.valid library storedPlan
  ... | false = inj₁ mismatch
  ... | true with Plan.textEqual (Plan.Saved.operation storedPlan) (toList "review_experience")
  ... | false = inj₁ mismatch
  ... | true with Independent.ProviderSettings.admitted (Store.BindingRow.settings binding)
  ... | false = inj₁ mismatch
  ... | true with arguments (Store.BindingRow.arguments binding)
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ input with Plan.stepsEqual (expectedSteps input) (Plan.Saved.steps storedPlan)
  ... | false = inj₁ mismatch
  ... | true = inj₂ (input , Store.ReservationRow.reservedAt reserved)

  Internal = ℕ × Metadata
  admit : Internal → Step.Registration → Maybe B.Diagnostic
  admit (token , metadata) registration with original token registration
  ... | inj₁ fault = just (inj₁ fault)
  ... | inj₂ _ = nothing

  decide : Internal → Store.World → B.Outcome
  decide (token , metadata) before with original token (Step.registration before)
  ... | inj₁ fault = inj₁ (inj₁ fault)
  ... | inj₂ (input , reservationTime) = proj₁ (B.checked token input metadata before)

  keepsJournal : ∀ input before after reply → decide input before ≡ inj₂ (after , reply) →
    Store.World.operations after ≡ Store.World.operations before
  keepsJournal (token , metadata) before after reply accepted with original token (Step.registration before)
  ... | inj₁ fault with accepted
  ... | ()
  keepsJournal (token , metadata) before after reply accepted | inj₂ (input , reservationTime) =
    B.checkedKeepsJournal token input metadata before after reply accepted

  module Saved = Step.Admitted Internal B.Diagnostic proj₁ (λ input → key (proj₁ input))
    (λ input → distinct (proj₁ input)) decide keepsJournal admit
  module K = Saved.Kernel

  decidesBound : ∀ token metadata before input reservationTime →
    original token (Step.registration before) ≡ inj₂ (input , reservationTime) →
    decide (token , metadata) before ≡ proj₁ (B.checked token input metadata before)
  decidesBound token metadata before input reservationTime bound rewrite bound = refl

  FreshGoal : ℕ → Request → Metadata → ℤ → Store.World → Store.World → Saved.Reply → Set
  FreshGoal token input metadata reservationTime before after (Step.done reply) = Σ Store.World (λ changed →
    B.Goal token input metadata before (inj₂ (changed , reply)) × after ≡ K.publication (token , metadata) changed reply)
  FreshGoal token input metadata reservationTime before after (Step.needsInput diagnostic) =
    after ≡ before × B.Goal token input metadata before (inj₁ diagnostic)
  FreshGoal token input metadata reservationTime before after _ = ⊥

  freshMeaning : ∀ token input metadata reservationTime before →
    original token (Step.registration before) ≡ inj₂ (input , reservationTime) →
    FreshGoal token input metadata reservationTime before (proj₁ (K.fresh (token , metadata) before)) (proj₂ (K.fresh (token , metadata) before))
  freshMeaning token input metadata reservationTime before bound rewrite decidesBound token metadata before input reservationTime bound
    with B.checked token input metadata before
  ... | inj₁ diagnostic , correct = refl , correct
  ... | inj₂ (changed , reply) , correct = changed , correct , refl

  MetaGoal : ℕ → Metadata → Store.World → Store.World → Saved.Reply → Set
  MetaGoal token metadata before after reply with original token (Step.registration before)
  ... | inj₁ fault = after ≡ before × reply ≡ Step.needsInput (inj₁ fault)
  ... | inj₂ (input , reservationTime) with Store.lookupCancellation before token
  ... | just cancelled = after ≡ before × reply ≡ Step.cancelled cancelled
  ... | nothing with Store.lookupSaved before token (key token) | Store.lookupSaved before token Step.resultKey
  ... | just saved | just _ = after ≡ before × reply ≡ Step.done saved
  ... | just _ | nothing = after ≡ before × reply ≡ Step.needsRecovery
  ... | nothing | just _ = after ≡ before × reply ≡ Step.needsRecovery
  ... | nothing | nothing = FreshGoal token input metadata reservationTime before after reply

  meaning : ∀ token metadata before →
    MetaGoal token metadata before (proj₁ (Saved.execute (token , metadata) before)) (proj₂ (Saved.execute (token , metadata) before))
  meaning token metadata before with original token (Step.registration before) in bound
  ... | inj₁ fault = refl , refl
  ... | inj₂ (input , reservationTime) with Store.lookupCancellation before token
  ... | just _ = refl , refl
  ... | nothing with Store.lookupSaved before token (key token) | Store.lookupSaved before token Step.resultKey
  ... | just _ | just _ = refl , refl
  ... | just _ | nothing = refl , refl
  ... | nothing | just _ = refl , refl
  ... | nothing | nothing = freshMeaning token input metadata reservationTime before bound

  record SavedOriginal (token : ℕ) (after : Store.World) (reply : Wire.Value) : Set where
    constructor savedOriginal
    field
      active : Store.lookupCancellation after token ≡ nothing
      step : Store.lookupSaved after token (key token) ≡ just reply
      final : Σ Wire.Value (λ value → Store.lookupSaved after token Step.resultKey ≡ just value)

  kernelDone : ∀ token metadata before reply →
    proj₂ (K.execute (token , metadata) before) ≡ Step.done reply →
    SavedOriginal token (proj₁ (K.execute (token , metadata) before)) reply
  kernelDone token metadata before reply completed
    with Store.lookupCancellation before token in active
  ... | just _ with completed
  ... | ()
  kernelDone token metadata before reply completed | nothing
    with Store.lookupSaved before token (key token) in step
       | Store.lookupSaved before token Step.resultKey in final
  ... | just saved | just value with completed
  ... | refl = savedOriginal active step (value , final)
  kernelDone token metadata before reply () | nothing | just _ | nothing
  kernelDone token metadata before reply () | nothing | nothing | just _
  kernelDone token metadata before reply completed | nothing | nothing | nothing
    with decide (token , metadata) before in accepted
  ... | inj₁ _ with completed
  ... | ()
  kernelDone token metadata before reply completed | nothing | nothing | nothing | inj₂ (changed , value)
    with completed
  ... | refl = savedOriginal
    (trans (K.publicationKeepsCancellation (token , metadata) before changed value accepted) active)
    (K.publishedStepReadable (token , metadata) before changed value accepted step)
    (value , K.publishedResultReadable (token , metadata) before changed value accepted final)

  executesBound : ∀ token metadata before input time →
    original token (Step.registration before) ≡ inj₂ (input , time) →
    Saved.execute (token , metadata) before ≡ K.execute (token , metadata) before
  executesBound token metadata before input time bound rewrite bound = refl

  kernelStableDone : ∀ token first second before value →
    proj₂ (K.execute (token , first) before) ≡ Step.done value →
    K.execute (token , second) (proj₁ (K.execute (token , first) before)) ≡ K.execute (token , first) before
  kernelStableDone token first second before value completed = trans
    (K.replay (token , second) _ value (proj₁ (SavedOriginal.final saved))
      (SavedOriginal.active saved) (SavedOriginal.step saved) (proj₂ (SavedOriginal.final saved)))
    (cong (λ reply → proj₁ (K.execute (token , first) before) , reply) (sym completed))
    where saved = kernelDone token first before value completed

  doneStable : ∀ token first second before value →
    proj₂ (Saved.execute (token , first) before) ≡ Step.done value →
    Saved.execute (token , second) (proj₁ (Saved.execute (token , first) before)) ≡
      Saved.execute (token , first) before
  doneStable token first second before value completed
    with original token (Step.registration before) in bound
  ... | inj₁ _ with completed
  ... | ()
  doneStable token first second before value completed | inj₂ (input , time) = trans
    (executesBound token second (proj₁ (K.execute (token , first) before)) input time
      (trans (cong (original token) (K.registrationUnchanged (token , first) before)) bound))
    (kernelStableDone token first second before value completed)

  Effect = ℕ
  Reply : Effect → Set
  Reply _ = Metadata × Saved.Reply

  Atomic : Store.World → (token : Effect) → Reply token → Store.World → Set
  Atomic before token (metadata , reply) after = Saved.Atomic before (token , metadata) reply after

  module X = Recovery.Execution Store.World Effect Reply Atomic
  module E = X.E

  script : ℕ → E.Script Saved.Reply
  script token = E.ask token (λ reply → E.done (proj₂ reply))

  atomicObservation : ∀ token before after metadata reply → Atomic before token (metadata , reply) after →
    (after , reply) ≡ Saved.execute (token , metadata) before
  atomicObservation token before after metadata reply physical =
    Saved.atomicObservation (token , metadata) before after reply physical

  completedObservation : ∀ token before after reply → X.Completed (script token) before after reply →
    Σ Metadata (λ metadata → (after , reply) ≡ Saved.execute (token , metadata) before)
  completedObservation token before after reply
    (X.completed _ (E.replied _ _ (metadata , _) (E.returned _))
      (X.changed _ _ _ _ physical (X.unchanged _))) =
    metadata , atomicObservation token before after metadata reply physical

  -- Refused/paused attempts have an aborted receipt and leave the starting
  -- world intact. A committed attempt carries the original saved answer.
  data InterruptOutcome (token : ℕ) (before after : Store.World) : Set where
    unchanged : after ≡ before → InterruptOutcome token before after
    published : ∀ metadata value → (after , Step.done value) ≡ Saved.execute (token , metadata) before →
      InterruptOutcome token before after

  interruptedAtomic : ∀ token before after metadata reply → Atomic before token (metadata , reply) after →
    InterruptOutcome token before after
  interruptedAtomic token before after metadata (Step.done value) physical =
    published metadata value (Saved.atomicObservation (token , metadata) before after (Step.done value) physical)
  interruptedAtomic token before .before metadata (Step.needsInput _) (observation , DB.abortedNone) = unchanged refl
  interruptedAtomic token before .before metadata Step.needsRecovery (observation , DB.abortedNone) = unchanged refl
  interruptedAtomic token before .before metadata (Step.cancelled _) (observation , DB.abortedNone) = unchanged refl

  interruptionState : ∀ token before after → X.Interrupted (script token) before after →
    InterruptOutcome token before after
  interruptionState token before after (X.atPrefix _ _ _ (E.stopped _) (X.unchanged _)) = unchanged refl
  interruptionState token before after
    (X.atPrefix _ _ _ (E.replied _ _ (metadata , reply) (E.stopped _))
      (X.changed _ _ _ _ physical (X.unchanged _))) = interruptedAtomic token before after metadata reply physical
  interruptionState token before after
    (X.beforeReply _ _ _ _ (metadata , reply) _ (E.stopped _) (X.unchanged _) physical) =
    interruptedAtomic token before after metadata reply physical
  interruptionState token before after (X.beforeReply _ _ _ _ _ _ (E.replied _ _ _ ()) _ _)

  Goal : ℕ → Store.World → Store.World → Saved.Reply → Set
  Goal token before after reply = Σ Metadata (λ metadata → MetaGoal token metadata before after reply)

  fromObservation : ∀ token metadata before after reply → (after , reply) ≡ Saved.execute (token , metadata) before → Goal token before after reply
  fromObservation token metadata before after reply observation = metadata , subst
    (λ outcome → MetaGoal token metadata before (proj₁ outcome) (proj₂ outcome)) (sym observation) (meaning token metadata before)

  converges : ∀ token before interrupted after reply → X.Interrupted (script token) before interrupted →
    X.Completed (script token) interrupted after reply → Goal token before after reply
  converges token before interrupted after reply interruption completion
    with interruptionState token before interrupted interruption | completedObservation token interrupted after reply completion
  ... | unchanged refl | metadata , observation = fromObservation token metadata before after reply observation
  ... | published first value same | second , observation = fromObservation token first before after reply
    (trans observation (trans (cong (Saved.execute (token , second)) (cong proj₁ same))
      (doneStable token first second before value (sym (cong proj₂ same)))))

  module Collected (token : ℕ) (before : Store.World) where
    metadata : Metadata
    metadata = Dependencies.observation dependencies token before
  progress : ∀ token before → Σ Store.World (λ after → Σ Saved.Reply (λ reply → X.Completed (script token) before after reply))
  progress token before = proj₁ executionResult , proj₂ executionResult , X.completed
    ((token , metadata , proj₂ executionResult) ∷ [])
    (E.replied token (λ reply → E.done (proj₂ reply)) (metadata , proj₂ executionResult) (E.returned _))
    (X.changed before token _ _
      (refl , Saved.expectedPhysical (token , metadata) before) (X.unchanged _))
    where
    metadata = Collected.metadata token before
    executionResult = Saved.execute (token , metadata) before

  everyDatabaseReceiptCovered : ∀ token metadata before → ∀ tag actual →
    DB.Atomic before (proj₁ (Saved.execute (token , metadata) before)) tag actual → X.Interrupted (script token) before actual
  everyDatabaseReceiptCovered token metadata before .DB.committed _ DB.committedAll =
    X.beforeReply [] token (λ reply → E.done (proj₂ reply)) before
      (metadata , proj₂ (Saved.execute (token , metadata) before)) _
      (E.stopped _) (X.unchanged before) (refl , Saved.expectedPhysical (token , metadata) before)
  everyDatabaseReceiptCovered token metadata before .DB.aborted _ DB.abortedNone =
    X.atPrefix [] (script token) before (E.stopped _) (X.unchanged before)
  everyDatabaseReceiptCovered token metadata before .DB.acknowledgementLost _ DB.unknownBefore =
    X.atPrefix [] (script token) before (E.stopped _) (X.unchanged before)
  everyDatabaseReceiptCovered token metadata before .DB.acknowledgementLost _ DB.unknownAfter =
    X.beforeReply [] token (λ reply → E.done (proj₂ reply)) before
      (metadata , proj₂ (Saved.execute (token , metadata) before)) _
      (E.stopped _) (X.unchanged before) (refl , Saved.expectedPhysical (token , metadata) before)

  operation : Recovery.RecoverableFor Store.World ℕ Saved.Reply Goal
  operation = record { Effect = Effect; Reply = Reply; script = script; Atomic = Atomic; converges = converges; progress = progress }

  executeKeepsRegistration : ∀ token metadata before →
    Step.registration (proj₁ (Saved.execute (token , metadata) before)) ≡ Step.registration before
  executeKeepsRegistration token metadata before with admit (token , metadata) (Step.registration before)
  ... | just _ = refl
  ... | nothing = K.registrationUnchanged (token , metadata) before

  interruptedKeepsRegistration : ∀ token before interrupted →
    X.Interrupted (script token) before interrupted → Step.registration interrupted ≡ Step.registration before
  interruptedKeepsRegistration token before interrupted interruptedRun with interruptionState token before interrupted interruptedRun
  ... | unchanged refl = refl
  ... | published metadata value observed = trans (cong Step.registration (cong proj₁ observed))
    (executeKeepsRegistration token metadata before)

  -- A first final publication adds exactly its step/result pair around a
  -- business world whose operation rows were unchanged. This is the bridge
  -- to the prefix's application-owned complete-journal readback check.
  firstPublication : ∀ token metadata before after value →
    Store.lookupSaved before token (key token) ≡ nothing → Store.lookupSaved before token Step.resultKey ≡ nothing →
    (after , Step.done value) ≡ Saved.execute (token , metadata) before →
    Σ Store.World (λ changed → decide (token , metadata) before ≡ inj₂ (changed , value) ×
      after ≡ K.publication (token , metadata) changed value)
  firstPublication token metadata before after value emptyStep emptyResult observed
    with admit (token , metadata) (Step.registration before)
  ... | just _ with observed
  ... | ()
  firstPublication token metadata before after value emptyStep emptyResult observed | nothing
    with Store.lookupCancellation before token
  ... | just _ with observed
  ... | ()
  firstPublication token metadata before after value emptyStep emptyResult observed | nothing | nothing
    rewrite emptyStep | emptyResult with decide (token , metadata) before in accepted
  ... | inj₁ _ with observed
  ... | ()
  firstPublication token metadata before after value emptyStep emptyResult observed | nothing | nothing | inj₂ (changed , answer)
    with observed
  ... | refl = changed , refl , refl

-- This private provider stage has no database publication effect. A ready
-- batch contains one actual usable response for every selected new belief;
-- patterns are allocated only by the final review transaction.
module ProviderStage (token : ℕ) (input : Request) (allocations : Preparing.Allocations)
  (backend : Store.World → Preparing.Claim → Text ⊎ List Store.Vector) where
  module Status = PreparationStatus
  module P = Preparing

  requiredIndices : List (ℕ × Candidates.Candidate) → List ℕ
  requiredIndices [] = []
  requiredIndices ((index , Candidates.patternCandidate _ _ _) ∷ rest) = requiredIndices rest
  requiredIndices ((index , Candidates.belief _ _ _ _) ∷ rest) = index ∷ requiredIndices rest

  Waiting : Store.World → Set
  Waiting before = Σ Observation.Snapshot (λ old → Σ (List (ℕ × Candidates.Candidate))
    (λ pending → Status.inspect input before ≡ Status.waiting old pending))

  record PacketFor (before : Store.World) (index : ℕ) (packet : Record.PreparedCandidate) : Set where
    constructor observedPacket
    field
      selected : P.Claim
      actualInput : P.makeClaim token input allocations index before ≡ inj₂ selected
      response : Text ⊎ List Store.Vector
      actualPacket : P.observe selected response ≡ inj₂ packet

  data Complete (before : Store.World) : List ℕ → List Record.PreparedCandidate → Set where
    none : Complete before [] []
    more : ∀ {index rest packet following} → PacketFor before index packet →
      Complete before rest following → Complete before (index ∷ rest) (packet ∷ following)

  data Collection (before : Store.World) (indices : List ℕ) : Set where
    failed : Validation.Fault → Collection before indices
    collected : ∀ packets → Complete before indices packets → Collection before indices

  data Result : Set where
    stopped : Validation.Fault → Result
    replayed : ∀ captured old → Status.inspect input captured ≡ Status.alreadyApplied old → Result
    preparedBatch : ∀ captured old pending → Status.inspect input captured ≡ Status.waiting old pending →
      ∀ packets → Complete captured (requiredIndices pending) packets → Result

  data SnapshotReceipt : Set where
    unavailable : Validation.Fault → SnapshotReceipt
    observedStore : Store.World → SnapshotReceipt

  data Effect : Set where
    snapshot : Effect
    embedding : ∀ captured index selected → Waiting captured →
      P.makeClaim token input allocations index captured ≡ inj₂ selected → Effect

  Reply : Effect → Set
  Reply snapshot = SnapshotReceipt
  Reply (embedding _ _ _ _ _) = Text ⊎ List Store.Vector

  Atomic : Store.World → (effect : Effect) → Reply effect → Store.World → Set
  Atomic before snapshot (unavailable _) after = after ≡ before
  Atomic before snapshot (observedStore captured) after = captured ≡ before × after ≡ before
  Atomic before (embedding captured _ _ _ _) response after = captured ≡ before × after ≡ before

  module X = Recovery.Execution Store.World Effect Reply Atomic
  module E = X.E

  mapScript : ∀ {A B : Set} → (A → B) → E.Script A → E.Script B
  mapScript f (E.done value) = E.done (f value)
  mapScript f (E.ask effect next) = E.ask effect (λ reply → mapScript f (next reply))

  mapRuns : ∀ {A B : Set} (f : A → B) {program : E.Script A} {events value} →
    E.Runs program events value → E.Runs (mapScript f program) events (f value)
  mapRuns f (E.returned value) = E.returned (f value)
  mapRuns f (E.replied effect next reply rest) = E.replied effect _ reply (mapRuns f rest)

  prepend : ∀ {captured index rest packet} → PacketFor captured index packet →
    Collection captured rest → Collection captured (index ∷ rest)
  prepend witnessed (failed fault) = failed fault
  prepend {packet = packet} witnessed (collected packets complete) = collected (packet ∷ packets) (more witnessed complete)

  mutual
    collect : ∀ captured indices → Waiting captured → E.Script (Collection captured indices)
    collect captured [] waiting = E.done (collected [] none)
    collect captured (index ∷ rest) waiting = afterClaim captured index rest waiting
      (P.makeClaim token input allocations index captured) refl

    afterClaim : ∀ captured index rest waiting observed →
      P.makeClaim token input allocations index captured ≡ observed → E.Script (Collection captured (index ∷ rest))
    afterClaim captured index rest waiting (inj₁ fault) actualInput = E.done (failed fault)
    afterClaim captured index rest waiting (inj₂ selected) actualInput =
      E.ask (embedding captured index selected waiting actualInput) λ response →
        afterEmbedding captured index rest waiting selected actualInput response (P.observe selected response) refl

    afterEmbedding : ∀ captured index rest waiting selected actualInput response observed →
      P.observe selected response ≡ observed → E.Script (Collection captured (index ∷ rest))
    afterEmbedding captured index rest waiting selected actualInput response (inj₁ fault) actualPacket = E.done (failed fault)
    afterEmbedding captured index rest waiting selected actualInput response (inj₂ packet) actualPacket =
      mapScript (prepend (observedPacket selected actualInput response actualPacket)) (collect captured rest waiting)

  finish : ∀ captured old pending → Status.inspect input captured ≡ Status.waiting old pending →
    Collection captured (requiredIndices pending) → Result
  finish captured old pending observed (failed fault) = stopped fault
  finish captured old pending observed (collected packets complete) = preparedBatch captured old pending observed packets complete

  afterStatus : ∀ captured status → Status.inspect input captured ≡ status → E.Script Result
  afterStatus captured (Status.blocked fault) observed = E.done (stopped fault)
  afterStatus captured (Status.alreadyApplied old) observed = E.done (replayed captured old observed)
  afterStatus captured (Status.waiting old pending) observed = mapScript (finish captured old pending observed)
    (collect captured (requiredIndices pending) (old , pending , observed))

  afterSnapshot : SnapshotReceipt → E.Script Result
  afterSnapshot (unavailable fault) = E.done (stopped fault)
  afterSnapshot (observedStore captured) = afterStatus captured (Status.inspect input captured) refl

  script : E.Script Result
  script = E.ask snapshot afterSnapshot

  atomicUnchanged : ∀ before effect reply after → Atomic before effect reply after → after ≡ before
  atomicUnchanged before snapshot (unavailable _) after physical = physical
  atomicUnchanged before snapshot (observedStore _) after physical = proj₂ physical
  atomicUnchanged before (embedding _ _ _ _ _) reply after physical = proj₂ physical

  changesUnchanged : ∀ {events before after} → X.Changes before events after → after ≡ before
  changesUnchanged (X.unchanged _) = refl
  changesUnchanged (X.changed before effect reply middle physical rest) = trans (changesUnchanged rest)
    (atomicUnchanged before effect reply middle physical)

  interruptedUnchanged : ∀ before after → X.Interrupted script before after → after ≡ before
  interruptedUnchanged before after (X.atPrefix _ _ _ _ changes) = changesUnchanged changes
  interruptedUnchanged before after (X.beforeReply _ effect next current reply _ _ changes physical) =
    trans (atomicUnchanged current effect reply after physical) (changesUnchanged changes)

  -- Every observed packet is held only in the owned call's result. No belief,
  -- vector, source record, history row or operation answer can appear here.
  preparationCannotPublish : ∀ before after result → X.Completed script before after result → after ≡ before
  preparationCannotPublish before after result (X.completed _ _ changes) = changesUnchanged changes

  mutual
    collectProgress : ∀ captured indices waiting → Σ (Collection captured indices) (λ result →
      Σ (List E.Event) (λ events → E.Runs (collect captured indices waiting) events result × X.Changes captured events captured))
    collectProgress captured [] waiting = collected [] none , [] , E.returned _ , X.unchanged captured
    collectProgress captured (index ∷ rest) waiting = claimProgress captured index rest waiting
      (P.makeClaim token input allocations index captured) refl

    claimProgress : ∀ captured index rest waiting observed actualInput →
      Σ (Collection captured (index ∷ rest)) (λ result → Σ (List E.Event) (λ events →
        E.Runs (afterClaim captured index rest waiting observed actualInput) events result × X.Changes captured events captured))
    claimProgress captured index rest waiting (inj₁ fault) actualInput = failed fault , [] , E.returned _ , X.unchanged captured
    claimProgress captured index rest waiting (inj₂ selected) actualInput
      with embeddingProgress captured index rest waiting selected actualInput (backend captured selected)
        (P.observe selected (backend captured selected)) refl
    ... | result , events , execution , physical = result ,
      (embedding captured index selected waiting actualInput , backend captured selected) ∷ events ,
      E.replied _ _ _ execution , X.changed captured _ _ captured (refl , refl) physical

    embeddingProgress : ∀ captured index rest waiting selected actualInput response observed actualPacket →
      Σ (Collection captured (index ∷ rest)) (λ result → Σ (List E.Event) (λ events →
        E.Runs (afterEmbedding captured index rest waiting selected actualInput response observed actualPacket) events result ×
        X.Changes captured events captured))
    embeddingProgress captured index rest waiting selected actualInput response (inj₁ fault) actualPacket =
      failed fault , [] , E.returned _ , X.unchanged captured
    embeddingProgress captured index rest waiting selected actualInput response (inj₂ packet) actualPacket
      with collectProgress captured rest waiting
    ... | following , events , execution , physical = prepend witnessed following , events ,
      mapRuns (prepend witnessed) execution , physical
      where witnessed = observedPacket selected actualInput response actualPacket

  data Captured (before : Store.World) : Result → Set where
    stoppedHere : ∀ fault → Captured before (stopped fault)
    replayHere : ∀ old observed → Captured before (replayed before old observed)
    batchHere : ∀ old pending observed packets complete →
      Captured before (preparedBatch before old pending observed packets complete)

  finishCaptured : ∀ captured old pending observed collection →
    Captured captured (finish captured old pending observed collection)
  finishCaptured captured old pending observed (failed fault) = stoppedHere fault
  finishCaptured captured old pending observed (collected packets complete) = batchHere old pending observed packets complete

  mappedResultCaptured : ∀ {A : Set} captured (f : A → Result) → (∀ value → Captured captured (f value)) →
    (program : E.Script A) → ∀ {events result} → E.Runs (mapScript f program) events result → Captured captured result
  mappedResultCaptured captured f correct (E.done value) (E.returned _) = correct value
  mappedResultCaptured captured f correct (E.ask effect next) (E.replied _ _ reply rest) =
    mappedResultCaptured captured f correct (next reply) rest

  afterStatusCaptured : ∀ captured status observed events result → E.Runs (afterStatus captured status observed) events result →
    Captured captured result
  afterStatusCaptured captured (Status.blocked fault) observed events result (E.returned _) = stoppedHere fault
  afterStatusCaptured captured (Status.alreadyApplied old) observed events result (E.returned _) = replayHere old observed
  afterStatusCaptured captured (Status.waiting old pending) observed events result execution =
    mappedResultCaptured captured (finish captured old pending observed) (finishCaptured captured old pending observed)
      (collect captured (requiredIndices pending) (old , pending , observed)) execution

  afterSnapshotCaptured : ∀ captured events result → E.Runs (afterSnapshot (observedStore captured)) events result →
    Captured captured result
  afterSnapshotCaptured captured = afterStatusCaptured captured (Status.inspect input captured) refl

  Goal : Store.World → Store.World → Result → Set
  Goal before after result = after ≡ before × Captured before result

  completedGoal : ∀ before after result → X.Completed script before after result → Goal before after result
  completedGoal before after .(stopped fault)
    (X.completed _ (E.replied snapshot _ (unavailable fault) (E.returned _)) physical) =
    changesUnchanged physical , stoppedHere fault
  completedGoal before after result
    (X.completed _ (E.replied snapshot _ (observedStore captured) execution)
      (X.changed _ _ _ middle physical rest)) =
    trans (changesUnchanged rest) (proj₂ physical) ,
      subst (λ world → Captured world result) (proj₁ physical) (afterSnapshotCaptured captured _ result execution)

  converges : ∀ before interrupted after result → X.Interrupted script before interrupted →
    X.Completed script interrupted after result → Goal before after result
  converges before interrupted after result interruption completion with interruptedUnchanged before interrupted interruption
  ... | refl = completedGoal before after result completion

  afterStatusProgress : ∀ before status observed → Σ Result (λ result → Σ (List E.Event)
    (λ events → E.Runs (afterStatus before status observed) events result × X.Changes before events before))
  afterStatusProgress before (Status.blocked fault) observed = stopped fault , [] , E.returned _ , X.unchanged before
  afterStatusProgress before (Status.alreadyApplied old) observed = replayed before old observed , [] , E.returned _ , X.unchanged before
  afterStatusProgress before (Status.waiting old pending) observed with collectProgress before (requiredIndices pending) (old , pending , observed)
  ... | collectedValue , events , execution , physical = finish before old pending observed collectedValue , events ,
    mapRuns (finish before old pending observed) execution , physical

  afterSnapshotProgress : ∀ before → Σ Result (λ result → Σ (List E.Event)
    (λ events → E.Runs (afterSnapshot (observedStore before)) events result × X.Changes before events before))
  afterSnapshotProgress before = afterStatusProgress before (Status.inspect input before) refl

  progress : ∀ before → Σ Result (λ result → X.Completed script before before result)
  progress before with afterSnapshotProgress before
  ... | result , events , execution , physical = result , X.completed
    ((snapshot , observedStore before) ∷ events)
    (E.replied snapshot afterSnapshot (observedStore before) execution)
    (X.changed before snapshot (observedStore before) before (refl , refl) physical)

-- After the concrete owner prefix, actual provider responses supply the
-- prepared data for the final transaction. The final reply cannot substitute
-- another packet list, and interrupted preparation leaves the store intact.
module AfterOwners (library : Library.Contract) (format : Encoding.Formatting) (database : ℕ)
  (databaseSum : List Float → Float) (calculator : Posterior.Calculator) (dependencies : Dependencies)
  (token : ℕ) (input : Request) (allocations : Preparing.Allocations)
  (backend : Store.World → Preparing.Claim → Text ⊎ List Store.Vector) where
  module P = ProviderStage token input allocations backend
  module F = FinalBody library format database databaseSum calculator dependencies
  Result = F.Saved.Reply

  supplied : List Record.PreparedCandidate → Metadata → Metadata
  supplied packets observed = record observed { prepared = packets }

  data Effect : Set where
    prepare : P.Effect → Effect
    finish : List Record.PreparedCandidate → Effect

  Reply : Effect → Set
  Reply (prepare effect) = P.Reply effect
  Reply (finish _) = Metadata × Result

  Atomic : Store.World → (effect : Effect) → Reply effect → Store.World → Set
  Atomic before (prepare effect) observed after = P.Atomic before effect observed after
  Atomic before (finish packets) (metadata , reply) after = F.Atomic before token (supplied packets metadata , reply) after

  module X = Recovery.Execution Store.World Effect Reply Atomic
  module E = X.E

  liftPreparation : ∀ {R} → P.E.Script R → E.Script R
  liftPreparation (P.E.done result) = E.done result
  liftPreparation (P.E.ask effect next) = E.ask (prepare effect) (λ observed → liftPreparation (next observed))

  event : P.E.Event → E.Event
  event (effect , observed) = prepare effect , observed

  liftRuns : ∀ {R} {program : P.E.Script R} {events result} → P.E.Runs program events result →
    E.Runs (liftPreparation program) (map event events) result
  liftRuns (P.E.returned result) = E.returned result
  liftRuns (P.E.replied effect next observed rest) = E.replied _ _ observed (liftRuns rest)

  liftChanges : ∀ {before events after} → P.X.Changes before events after → X.Changes before (map event events) after
  liftChanges (P.X.unchanged before) = X.unchanged before
  liftChanges (P.X.changed before effect observed middle physical rest) = X.changed before _ _ middle physical (liftChanges rest)

  final : List Record.PreparedCandidate → E.Script Result
  final packets = E.ask (finish packets) (λ observed → E.done (proj₂ observed))

  afterPreparation : P.Result → E.Script Result
  afterPreparation (P.stopped fault) = E.done (Step.needsInput (inj₁ fault))
  afterPreparation (P.replayed _ _ _) = final []
  afterPreparation (P.preparedBatch _ _ _ _ packets _) = final packets

  script : E.Script Result
  script = E._>>=_ (liftPreparation P.script) afterPreparation

  data Ready : P.Result → List Record.PreparedCandidate → Set where
    replay : ∀ captured old observed → Ready (P.replayed captured old observed) []
    batch : ∀ captured old pending observed packets complete →
      Ready (P.preparedBatch captured old pending observed packets complete) packets

  data Goal (before after : Store.World) : Result → Set where
    preparationStopped : ∀ fault → after ≡ before → Goal before after (Step.needsInput (inj₁ fault))
    reviewAttempted : ∀ prepared packets metadata reply → P.Captured before prepared → Ready prepared packets →
      F.MetaGoal token (supplied packets metadata) before after reply → Goal before after reply

  finalProgress : ∀ packets before → Σ Store.World (λ after → Σ Result (λ reply → X.Completed (final packets) before after reply))
  finalProgress packets before = proj₁ expected , proj₂ expected , X.completed
    ((finish packets , metadata , proj₂ expected) ∷ []) (E.replied _ _ _ (E.returned _))
    (X.changed before _ _ _ (refl , F.Saved.expectedPhysical (token , supplied packets metadata) before) (X.unchanged _))
    where
    metadata = Dependencies.observation dependencies token before
    expected = F.Saved.execute (token , supplied packets metadata) before

  afterPreparationProgress : ∀ prepared before → Σ Store.World (λ after → Σ Result
    (λ reply → X.Completed (afterPreparation prepared) before after reply))
  afterPreparationProgress (P.stopped fault) before = before , Step.needsInput (inj₁ fault) , X.completed [] (E.returned _) (X.unchanged before)
  afterPreparationProgress (P.replayed _ _ _) before = finalProgress [] before
  afterPreparationProgress (P.preparedBatch _ _ _ _ packets _) before = finalProgress packets before

  progress : ∀ before → Σ Store.World (λ after → Σ Result (λ reply → X.Completed script before after reply))
  progress before with P.progress before
  ... | prepared , P.X.completed firstEvents firstRun firstChanges with afterPreparationProgress prepared before
  ... | after , reply , X.completed laterEvents laterRun laterChanges = after , reply , X.completed _
    (E.bindRuns (liftRuns firstRun) laterRun) (X.changesAppend (liftChanges firstChanges) laterChanges)

  splitPreparation : ∀ (program : P.E.Script P.Result) before after reply {events} →
    E.Runs (E._>>=_ (liftPreparation program) afterPreparation) events reply → X.Changes before events after →
    Σ Store.World (λ middle → Σ P.Result (λ prepared →
      P.X.Completed program before middle prepared × X.Completed (afterPreparation prepared) middle after reply))
  splitPreparation (P.E.done prepared) before after reply execution physical = before , prepared ,
    P.X.completed [] (P.E.returned _) (P.X.unchanged before) , X.completed _ execution physical
  splitPreparation (P.E.ask effect next) before after reply (E.replied _ _ observed execution)
    (X.changed _ _ _ middle physical later)
    with splitPreparation (next observed) middle after reply execution later
  ... | baseline , prepared , P.X.completed events firstRun firstChanges , finished = baseline , prepared ,
    P.X.completed ((effect , observed) ∷ events) (P.E.replied effect next observed firstRun)
      (P.X.changed before effect observed middle physical firstChanges) , finished

  finalMeaning : ∀ prepared packets before after reply → P.Captured before prepared → Ready prepared packets →
    X.Completed (final packets) before after reply → Goal before after reply
  finalMeaning prepared packets before after reply captured ready
    (X.completed _ (E.replied _ _ (metadata , _) (E.returned _))
      (X.changed _ _ _ _ physical (X.unchanged _))) =
    reviewAttempted prepared packets metadata reply captured ready
      (subst (λ result → F.MetaGoal token (supplied packets metadata) before (proj₁ result) (proj₂ result))
        (sym (F.atomicObservation token before after (supplied packets metadata) reply physical))
        (F.meaning token (supplied packets metadata) before))

  afterPreparationMeaning : ∀ prepared before after reply → P.Captured before prepared →
    X.Completed (afterPreparation prepared) before after reply → Goal before after reply
  afterPreparationMeaning (P.stopped fault) before .before .(Step.needsInput (inj₁ fault)) captured
    (X.completed [] (E.returned _) (X.unchanged _)) = preparationStopped fault refl
  afterPreparationMeaning prepared@(P.replayed captured old observed) before after reply valid finished =
    finalMeaning prepared [] before after reply valid (replay captured old observed) finished
  afterPreparationMeaning prepared@(P.preparedBatch captured old pending observed packets complete) before after reply valid finished =
    finalMeaning prepared packets before after reply valid (batch captured old pending observed packets complete) finished

  completedGoal : ∀ before after reply → X.Completed script before after reply → Goal before after reply
  completedGoal before after reply (X.completed events execution physical)
    with splitPreparation P.script before after reply execution physical
  ... | middle , prepared , preparation , publication with P.completedGoal before middle prepared preparation
  ... | refl , captured = afterPreparationMeaning prepared before after reply captured publication

  data Cut (before after : Store.World) : Set where
    noPublication : after ≡ before → Cut before after
    published : ∀ prepared packets metadata value → P.Captured before prepared → Ready prepared packets →
      (after , Step.done value) ≡ F.Saved.execute (token , supplied packets metadata) before → Cut before after

  finishAtomicCut : ∀ prepared packets before after metadata reply → P.Captured before prepared → Ready prepared packets →
    Atomic before (finish packets) (metadata , reply) after → Cut before after
  finishAtomicCut prepared packets before after metadata (Step.done value) captured ready physical =
    published prepared packets metadata value captured ready (F.atomicObservation token before after (supplied packets metadata) (Step.done value) physical)
  finishAtomicCut prepared packets before .before metadata (Step.needsInput _) captured ready (observed , DB.abortedNone) = noPublication refl
  finishAtomicCut prepared packets before .before metadata Step.needsRecovery captured ready (observed , DB.abortedNone) = noPublication refl
  finishAtomicCut prepared packets before .before metadata (Step.cancelled _) captured ready (observed , DB.abortedNone) = noPublication refl

  doneInterruptedSameWorld : ∀ {R : Set} (value : R) before after → X.Interrupted (E.done value) before after → after ≡ before
  doneInterruptedSameWorld value before .before (X.atPrefix [] _ _ (E.stopped _) (X.unchanged _)) = refl
  doneInterruptedSameWorld value before after (X.beforeReply _ _ _ _ _ _ () _ _)

  finalCut : ∀ prepared packets before after → P.Captured before prepared → Ready prepared packets →
    X.Interrupted (final packets) before after → Cut before after
  finalCut prepared packets before .before captured ready (X.atPrefix [] _ _ (E.stopped _) (X.unchanged _)) = noPublication refl
  finalCut prepared packets before after captured ready
    (X.atPrefix _ _ _ (E.replied _ _ (metadata , reply) (E.stopped _))
      (X.changed _ _ _ _ physical (X.unchanged _))) = finishAtomicCut prepared packets before after metadata reply captured ready physical
  finalCut prepared packets before after captured ready
    (X.beforeReply [] _ _ _ (metadata , reply) _ (E.stopped _) (X.unchanged _) physical) =
    finishAtomicCut prepared packets before after metadata reply captured ready physical
  finalCut prepared packets before after captured ready (X.beforeReply _ _ _ _ _ _ (E.replied _ _ _ ()) _ _)

  afterPreparationCut : ∀ prepared before after → P.Captured before prepared →
    X.Interrupted (afterPreparation prepared) before after → Cut before after
  afterPreparationCut (P.stopped fault) before after captured interrupted =
    noPublication (doneInterruptedSameWorld (Step.needsInput (inj₁ fault)) before after interrupted)
  afterPreparationCut prepared@(P.replayed source old observed) before after captured interrupted =
    finalCut prepared [] before after captured (replay source old observed) interrupted
  afterPreparationCut prepared@(P.preparedBatch source old pending observed packets complete) before after captured interrupted =
    finalCut prepared packets before after captured (batch source old pending observed packets complete) interrupted

  prependPreparationInterruption : ∀ before effect (next : P.Reply effect → P.E.Script P.Result) observed middle after → P.Atomic before effect observed middle →
    P.X.Interrupted (next observed) middle after → P.X.Interrupted (P.E.ask effect next) before after
  prependPreparationInterruption before effect next observed middle after physical
    (P.X.atPrefix events residual _ prefix changes) = P.X.atPrefix ((effect , observed) ∷ events) residual after
      (P.E.replied effect next observed prefix) (P.X.changed before effect observed middle physical changes)
  prependPreparationInterruption before effect next observed middle after physical
    (P.X.beforeReply events active later current reply _ prefix changes actual) =
    P.X.beforeReply ((effect , observed) ∷ events) active later current reply after
      (P.E.replied effect next observed prefix) (P.X.changed before effect observed middle physical changes) actual

  data Phase (program : P.E.Script P.Result) (before after : Store.World) : Set where
    preparing : P.X.Interrupted program before after → Phase program before after
    finishing : ∀ baseline prepared → P.X.Completed program before baseline prepared →
      X.Interrupted (afterPreparation prepared) baseline after → Phase program before after

  prependPhase : ∀ before effect next observed middle after → P.Atomic before effect observed middle →
    Phase (next observed) middle after → Phase (P.E.ask effect next) before after
  prependPhase before effect next observed middle after physical (preparing interrupted) =
    preparing (prependPreparationInterruption before effect next observed middle after physical interrupted)
  prependPhase before effect next observed middle after physical
    (finishing baseline prepared (P.X.completed events execution changes) interrupted) =
    finishing baseline prepared (P.X.completed ((effect , observed) ∷ events)
      (P.E.replied effect next observed execution) (P.X.changed before effect observed middle physical changes)) interrupted

  splitInterrupted : ∀ (program : P.E.Script P.Result) before after →
    X.Interrupted (E._>>=_ (liftPreparation program) afterPreparation) before after → Phase program before after
  splitInterrupted (P.E.done prepared) before after interrupted =
    finishing before prepared (P.X.completed [] (P.E.returned prepared) (P.X.unchanged before)) interrupted
  splitInterrupted (P.E.ask effect next) before .before
    (X.atPrefix [] _ _ (E.stopped _) (X.unchanged _)) = preparing (P.X.atPrefix [] _ before (P.E.stopped _) (P.X.unchanged before))
  splitInterrupted (P.E.ask effect next) before after
    (X.atPrefix _ residual _ (E.replied _ _ observed prefix) (X.changed _ _ _ middle physical changes)) =
    prependPhase before effect next observed middle after physical
      (splitInterrupted (next observed) middle after (X.atPrefix _ residual after prefix changes))
  splitInterrupted (P.E.ask effect next) before after
    (X.beforeReply [] _ _ _ observed _ (E.stopped _) (X.unchanged _) physical) =
    preparing (P.X.beforeReply [] effect next before observed after (P.E.stopped _) (P.X.unchanged before) physical)
  splitInterrupted (P.E.ask effect next) before after
    (X.beforeReply _ active later current reply _ (E.replied _ _ observed prefix)
      (X.changed _ _ _ middle physical changes) actual) =
    prependPhase before effect next observed middle after physical
      (splitInterrupted (next observed) middle after (X.beforeReply _ active later current reply after prefix changes actual))

  interruptionCut : ∀ before after → X.Interrupted script before after → Cut before after
  interruptionCut before after interrupted with splitInterrupted P.script before after interrupted
  ... | preparing cut = noPublication (P.interruptedUnchanged before after cut)
  ... | finishing baseline prepared providerDone cut with P.completedGoal before baseline prepared providerDone
  ... | refl , captured = afterPreparationCut prepared before after captured cut
