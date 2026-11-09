{-# OPTIONS --safe #-}
-- The business meaning of a fresh, admitted source publication. Allocation
-- observations determine canonical items; no caller supplies a normalized row.
-- ExperienceSourceRecovery connects this outcome to admitted registered runs.
module Mimir.ExperienceSourceIntent where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Float.Base using (Float)
open import Data.Integer using (ℤ; +_)
open import Data.List using (List; []; _∷_; _++_; map; concatMap)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _≟_; z≤n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst; trans)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.LearningStore as Learning
import Mimir.ExperienceRead as Read
import Mimir.ExperienceSchema as Source
import Mimir.ExperienceRecord as Recording
import Mimir.LearningInput as Input
import Mimir.LearningNormalization as Normalization
import Mimir.LearningOperations as Operations
import Mimir.LearningSchema as Items
import Mimir.ReviewObservation as Observation
import Mimir.ReviewPreparationPublication as Publication
import Mimir.ReviewLedger as Ledger
import Mimir.ReviewEdges as Edges
import Mimir.ReviewNumericalPublication as Numerical
import Mimir.ReviewSchema as Review
import Mimir.LearningHistoryWire as History
import Mimir.PublicEncoding as Encoding
import Mimir.StructuredValue as Wire
import Mimir.InferenceStorageBinding as Inference
import Mimir.InferenceProtocol as Infer
import Mimir.StorageSemantics as Storage
import Mimir.LearningRecompute as Recompute
import Mimir.PosteriorComputation as Posterior
import Mimir.GroundingRecovery as Grounding
import Mimir.Validation
import Mimir.CandidateGraph

rightInjective : ∀ {A B : Set} {first second : B} →
  inj₂ {A = A} first ≡ inj₂ second → first ≡ second
rightInjective refl = refl

readNewHead : ∀ value now rest → Read.get
  (Source.Experience.identity (Observation.Snapshot.experience value)) (Read.row value now ∷ rest) ≡
  just (Read.storedSnapshot (Read.row value now))
readNewHead value now rest with Source.Experience.identity (Observation.Snapshot.experience value) ≟
  Source.Experience.identity (Observation.Snapshot.experience value)
... | yes _ = refl
... | no impossible = ⊥-elim (impossible refl)

readPut : ∀ value now rows → Read.get
  (Source.Experience.identity (Observation.Snapshot.experience value)) (Learning.put value now rows) ≡
  just (Read.storedSnapshot (Read.row value now))
readPut value now [] = readNewHead value now []
readPut value now (old ∷ rest) with Source.Experience.identity (Observation.Snapshot.experience value) ≟ Read.identity old in seen
... | yes _ = readNewHead value now rest
... | no _ rewrite seen = readPut value now rest

-- Return the complete map exposed by native ExperienceState. It is derived
-- from the canonical stored items, not supplied alongside the source request.
itemIDs : List Items.LearningItem → List (Text × ℕ)
itemIDs [] = []
itemIDs (item ∷ rest) with Items.LearningItem.localKey item
... | nothing = itemIDs rest
... | just key = (key , Items.LearningItem.identity item) ∷ itemIDs rest

putHead : History.Head → List History.Head → List History.Head
putHead value [] = value ∷ []
putHead value (old ∷ rest) with History.Head.identity value ≟ History.Head.identity old
... | yes _ = value ∷ rest
... | no _ = old ∷ putHead value rest

snapshot : Source.Experience → ℕ → Store.World → Observation.Snapshot
snapshot value expected before = Recording.newSnapshot value (suc expected)
  (Read.get (Source.Experience.identity value) (Learning.World.current (Store.World.learning before)))

header : Observation.Snapshot → History.Head
header value = History.head (Source.Experience.identity (Observation.Snapshot.experience value))
  (Observation.Snapshot.revision value) (Observation.Snapshot.reviewRevision value)
  (Observation.Snapshot.reviewedRevision value) (Source.Experience.project (Observation.Snapshot.experience value))

roots : Source.Experience → Store.World → List ℕ
roots value before = Numerical.oldTargets (Ledger.activeApplied
  (Ledger.World.cells ledger (Source.Experience.identity value))
  (Ledger.World.histories ledger (Source.Experience.identity value)))
  where ledger = Publication.World.ledger (Learning.World.publication (Store.World.learning before))

-- Source publication invalidates the active pointer; it never deletes an
-- immutable review payload, including when no prior current source is read.
sourceLedger : Source.Experience → Maybe Observation.Snapshot → Ledger.World → Ledger.World
sourceLedger value (just old) prior = Ledger.correct (Source.Experience.identity value) prior
sourceLedger value nothing prior = Ledger.world
  (Ledger.Cells.write (Source.Experience.identity value)
    (Ledger.R.cell (Source.Experience.project value) 1 0 0 nothing z≤n) (Ledger.World.cells prior))
  (Ledger.World.histories prior)

module For (database : ℕ) (format : Encoding.Formatting)
  (databaseSum : List Float → Float) (calculator : Posterior.Calculator) where
  module Encode = Encoding.Encode format
  module Normalize = Normalization.For Operations.Failure Operations.allocationFailure database Operations.locateFailure
  module T = Normalize.T
  module B = Grounding.Business databaseSum calculator
  module N = Inference.NumericalOutcome databaseSum

  -- Interpret the actual replies to the exact pending per-key allocations.
  -- Extra or missing observations are not a completed preparation. This is
  -- internal trace validation, not a new agent request field or work limit.
  observe : ∀ {A : Set} → T.Allocation A → List (Operations.Failure ⊎ ℕ) → Maybe A
  observe (T.resolved value) [] = just value
  observe (T.resolved value) (_ ∷ _) = nothing
  observe (T.reserve experience key source actor next) [] = nothing
  observe (T.reserve experience key source actor next) (reply ∷ rest) = observe (next reply) rest

  observationsResolve : ∀ {A : Set} (program : T.Allocation A) replies result →
    observe program replies ≡ just result → T.Resolves program result
  observationsResolve (T.resolved value) [] .value refl = T.resolvedResult
  observationsResolve (T.resolved value) (_ ∷ _) result ()
  observationsResolve (T.reserve experience key source actor next) [] result ()
  observationsResolve (T.reserve experience key source actor next) (reply ∷ rest) result observed =
    T.reservedResult reply (observationsResolve (next reply) rest result observed)

  normalized : Input.Experience → Store.World → List (Operations.Failure ⊎ ℕ) →
    Maybe (Operations.Failure ⊎ (Learning.World × Source.Experience))
  normalized input before = observe (Normalize.experience input (Store.learningView before))

  NormalizationResult = Maybe (Operations.Failure ⊎ (Learning.World × Source.Experience))

  -- Every admitted source row, including its UUID, project, source records
  -- and non-item fields, comes from the submitted incident. Only item UUIDs
  -- are filled by the observed allocation program.
  normalizedKeepsIncident : ∀ input before replies staged canonical →
    normalized input before replies ≡ just (inj₂ (staged , canonical)) →
    Source.Experience.identity canonical ≡ Input.Experience.identity input
  normalizedFromInput : ∀ input before replies staged canonical →
    normalized input before replies ≡ just (inj₂ (staged , canonical)) →
    Σ (List Items.LearningItem) (λ assigned → canonical ≡ Input.canonicalExperience input assigned)
  normalizedFromInput input before replies staged canonical observed =
    let (_ , assigned) , first , remaining = Normalize.bindSuccess program continuation
          (staged , canonical) resolution
    in assigned , sym (cong proj₂ (rightInjective (T.resolvedValue remaining)))
    where
    program = Normalize.located (Mimir.Validation.key "experience" ∷ Mimir.Validation.key "learning_items" ∷ [])
      (Normalize.items (Input.Experience.identity input) (Input.Experience.items input) (Store.learningView before))
    continuation : Learning.World × List Items.LearningItem → T.Allocation
      (Operations.Failure ⊎ (Learning.World × Source.Experience))
    continuation (middle , assigned) = T.resolved (inj₂ (middle , Input.canonicalExperience input assigned))
    resolution = observationsResolve (Normalize.experience input (Store.learningView before)) replies _ observed

  normalizedKeepsIncident input before replies staged canonical observed =
    let assigned , same = normalizedFromInput input before replies staged canonical observed
    in cong Source.Experience.identity same

  sourceReply : Observation.Snapshot → Wire.Value
  sourceReply value = Wire.object
    ((toList "experience" , Encode.experience (Observation.Snapshot.experience value)) ∷
     (toList "revision" , Wire.signed (Observation.Snapshot.revision value)) ∷
     (toList "review_revision" , Wire.signed (Observation.Snapshot.reviewRevision value)) ∷
     (toList "reviewed_revision" , Wire.signed (Observation.Snapshot.reviewedRevision value)) ∷
     named (itemIDs (Source.Experience.items (Observation.Snapshot.experience value))))
    where
    named : List (Text × ℕ) → List (Text × Wire.Value)
    named [] = []
    named pairs@(_ ∷ _) = (toList "item_ids" , Wire.object (map (λ { (key , identity) → key , Encode.uuid identity }) pairs)) ∷ []

  -- A fresh source replaces its current version, appends immutable history,
  -- invalidates that source's review pointer/edges, and retains ownership.
  -- Raw history payloads coexist with typed rows so old JSON is not rewritten.
  intended : Source.Experience → ℕ → ℤ → Store.World → Store.World
  intended value expected sourceTime before = record before
    { learning = record learning
      { publication = record publication
        { ledger = sourceLedger value old (Publication.World.ledger publication)
        ; edges = Edges.replace (Source.Experience.identity value) [] (Publication.World.edges publication) }
      ; current = Learning.put result sourceTime (Learning.World.current learning)
      ; sources = Learning.sourceVersion value (suc expected) sourceTime ∷ Learning.World.sources learning }
    ; history = record prior
      { heads = putHead (header result) (History.Database.heads prior)
      ; sourceRows = History.row (Source.Experience.identity value) (+ suc expected) (+ suc expected)
          sourceTime (Encode.experience value) ∷ History.Database.sourceRows prior } }
    where
    learning = Store.World.learning before
    publication = Learning.World.publication learning
    prior = Store.World.history before
    old = Read.get (Source.Experience.identity value) (Learning.World.current learning)
    result = snapshot value expected before

  originalSourceHistoryRetained : ∀ value expected sourceTime before sourceRow →
    sourceRow ∈ History.Database.sourceRows (Store.World.history before) →
    sourceRow ∈ History.Database.sourceRows (Store.World.history (intended value expected sourceTime before))
  originalSourceHistoryRetained value expected sourceTime before sourceRow member = there member

  currentIsRequestedSource : ∀ value expected sourceTime before →
    Read.get (Source.Experience.identity value)
      (Learning.World.current (Store.World.learning (intended value expected sourceTime before))) ≡
    just (snapshot value expected before)
  currentIsRequestedSource value expected sourceTime before
    with Read.get (Source.Experience.identity value) (Learning.World.current (Store.World.learning before))
  ... | nothing = readPut (Recording.newSnapshot value (suc expected) nothing) sourceTime
    (Learning.World.current (Store.World.learning before))
  ... | just old = readPut (Recording.newSnapshot value (suc expected) (just old)) sourceTime
    (Learning.World.current (Store.World.learning before))

  nextRevision : ∀ value expected before →
    Observation.Snapshot.revision (snapshot value expected before) ≡ (+ suc expected)
  nextRevision value expected before with
    Read.get (Source.Experience.identity value) (Learning.World.current (Store.World.learning before))
  ... | nothing = refl
  ... | just _ = refl

  originalReviewHistoryRetained : ∀ value expected sourceTime before →
    History.Database.reviewRows (Store.World.history (intended value expected sourceTime before)) ≡
      History.Database.reviewRows (Store.World.history before)
  originalReviewHistoryRetained value expected sourceTime before = refl

  typedReviewHistoryRetained : ∀ value expected sourceTime before →
    Ledger.World.histories (Publication.World.ledger
      (Learning.World.publication (Store.World.learning (intended value expected sourceTime before)))) ≡
    Ledger.World.histories (Publication.World.ledger (Learning.World.publication (Store.World.learning before)))
  typedReviewHistoryRetained value expected sourceTime before
    with Read.get (Source.Experience.identity value) (Learning.World.current (Store.World.learning before))
  ... | nothing = refl
  ... | just _ = refl

  originalOwnershipRetained : ∀ value expected sourceTime before →
    Publication.World.owners (Learning.World.publication (Store.World.learning (intended value expected sourceTime before))) ≡
      Publication.World.owners (Learning.World.publication (Store.World.learning before))
  originalOwnershipRetained value expected sourceTime before = refl

  originalItemKeysRetained : ∀ value expected sourceTime before →
    Learning.World.itemKeys (Store.World.learning (intended value expected sourceTime before)) ≡
      Learning.World.itemKeys (Store.World.learning before)
  originalItemKeysRetained value expected sourceTime before = refl

  unrelatedPhysicalTablesRetained : ∀ value expected sourceTime before →
    let changed = intended value expected sourceTime before in
    (Store.World.chunks changed , Store.World.beliefVectors changed , Store.World.chunkVectors changed ,
      Store.World.grounds changed , Store.World.operations changed , Store.World.embeddingOwners changed) ≡
    (Store.World.chunks before , Store.World.beliefVectors before , Store.World.chunkVectors before ,
      Store.World.grounds before , Store.World.operations before , Store.World.embeddingOwners before)
  unrelatedPhysicalTablesRetained value expected sourceTime before = refl

  -- Derive exactly the native source project's reachable targets and active
  -- project reviews. A foreign root is refused; scope is never broadened.
  context : Source.Experience → List ℕ → Store.World → N.PreparationIssue ⊎ N.Context
  context value affected before with Recompute.owned project chosen
    where
    project = Source.Experience.project value
    chosen = Recompute.selected (Recompute.closure project (Store.beliefs before) (Storage.edges before) affected) (Store.beliefs before)
  ... | false = inj₁ N.invalidStoredInputs
  ... | true with Recompute.prepareNodes (concatMap Review.Review.feedbacks reviews)
      (Storage.groundTotals databaseSum before) chosen
    | Recompute.prepareEdges (map Mimir.CandidateGraph.BeliefValues.identity chosen) (Storage.edges before)
    where
    project = Source.Experience.project value
    chosen = Recompute.selected (Recompute.closure project (Store.beliefs before) (Storage.edges before) affected) (Store.beliefs before)
    reviews = Recompute.activeReviews project (Learning.identities (Store.World.learning before))
      (Publication.World.ledger (Learning.World.publication (Store.World.learning before)))
  ... | nothing | _ = inj₁ N.invalidStoredInputs
  ... | just _ | nothing = inj₁ N.invalidStoredInputs
  ... | just targets | just incoming = inj₂ (N.context false nothing
    (Recompute.external (map Posterior.Node.identity targets) (Store.beliefs before)) incoming targets)

  Outcome = B.Diagnostic ⊎ (Store.World × Wire.Value)

  SelectedGoal : Source.Experience → ℕ → ℤ → ℤ → Store.World → N.Context → Outcome → Set
  SelectedGoal value expected sourceTime posteriorTime before selected (inj₁ diagnostic) =
    B.Selected.DiagnosticGoal posteriorTime selected diagnostic
  SelectedGoal value expected sourceTime posteriorTime before selected (inj₂ (after , reply)) =
    Σ (List (ℕ × Float)) (λ numericalReply →
      N.Completed posteriorTime selected (intended value expected sourceTime before) after numericalReply ×
      reply ≡ sourceReply (snapshot value expected before))

  -- This goal states posterior equations on the complete source publication,
  -- rather than accepting whichever node list a calculation happened to return.
  Goal : Source.Experience → ℕ → ℤ → ℤ → Store.World → Outcome → Set
  Goal value expected sourceTime posteriorTime before outcome
    with context value (roots value before) (intended value expected sourceTime before)
  ... | inj₁ issue = outcome ≡ inj₁ (B.preparation issue)
  ... | inj₂ selected = SelectedGoal value expected sourceTime posteriorTime before selected outcome

  checked : ∀ value expected sourceTime posteriorTime before →
    Σ Outcome (Goal value expected sourceTime posteriorTime before)
  checked value expected sourceTime posteriorTime before with
    context value (roots value before) (intended value expected sourceTime before)
  ... | inj₁ issue = inj₁ (B.preparation issue) , refl
  ... | inj₂ selected = convert (B.Selected.checked posteriorTime selected (intended value expected sourceTime before))
    where
    convert : Σ B.Outcome (B.Selected.Goal posteriorTime selected (intended value expected sourceTime before)) →
      Σ Outcome (SelectedGoal value expected sourceTime posteriorTime before selected)
    convert (inj₁ diagnostic , correct) = inj₁ diagnostic , correct
    convert (inj₂ (after , _) , numericalReply , complete , _) =
      inj₂ (after , sourceReply (snapshot value expected before)) , numericalReply , complete , refl

  completedCurrentIsRequestedSource : ∀ value expected sourceTime posteriorTime before selected after numericalReply →
    N.Completed posteriorTime selected (intended value expected sourceTime before) after numericalReply →
    Read.get (Source.Experience.identity value) (Learning.World.current (Store.World.learning after)) ≡
      just (snapshot value expected before)
  completedCurrentIsRequestedSource value expected sourceTime posteriorTime before selected after numericalReply complete = trans
    (cong (λ state → Read.get (Source.Experience.identity value) (Learning.World.current (Store.World.learning state)))
      (N.completedPreservesOtherStoreComponents posteriorTime selected (intended value expected sourceTime before) after numericalReply complete))
    (currentIsRequestedSource value expected sourceTime before)

  publicationKeepsJournal : ∀ value expected sourceTime posteriorTime before after reply →
    Goal value expected sourceTime posteriorTime before (inj₂ (after , reply)) →
    Store.World.operations after ≡ Store.World.operations before
  publicationKeepsJournal value expected sourceTime posteriorTime before after reply correct with
    context value (roots value before) (intended value expected sourceTime before)
  ... | inj₁ issue with correct
  ... | ()
  publicationKeepsJournal value expected sourceTime posteriorTime before after reply correct | inj₂ selected =
    let numericalReply , complete , answered = correct
    in cong Store.World.operations (N.completedPreservesOtherStoreComponents posteriorTime selected
      (intended value expected sourceTime before) after numericalReply complete)

  -- Normalization operates on a read view whose grounding totals are derived.
  -- Publication installs only its actual key/owner changes, rather than copying
  -- that read view over unrelated physical state.
  installNormalization : Learning.World → Store.World → Store.World
  installNormalization staged before = record before { learning = record prior
    { itemKeys = Learning.World.itemKeys staged
    ; publication = record (Learning.World.publication prior)
      { owners = Publication.World.owners (Learning.World.publication staged) } } }
    where prior = Store.World.learning before

