{-# OPTIONS --safe #-}
-- A registered review derives its publication from the original request,
-- observed preparation packets and PostgreSQL allocation/clock receipts.
-- FinalBody certifies the final transaction only. The independently committed
-- owner prefix, provider ownership and initial saved-prefix admission must be
-- composed before this can be dispatched as the whole review operation.
module Mimir.ReviewPublicationRecovery where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Float.Base using (Float)
open import Data.Integer using (ℤ; ∣_∣; +_)
import Data.Integer.Properties as Integer
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; subst)
open import Relation.Binary.PropositionalEquality using (sym)
open import Relation.Nullary using (yes; no)
open import Mimir.Text using (Text)
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
