{-# OPTIONS --safe #-}
-- A backfill keeps its original source selection and truthful original counts.
-- Preparation is observed work; no caller supplies an expected vector/result.
module Mimir.BackfillRecovery where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.List using (List; []; _∷_; map; filterᵇ; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Properties as Maybes
open import Data.Nat using (ℕ; _≤?_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (does)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.ApplicationStore as Store
import Mimir.BeliefEmbedding as Backfill
import Mimir.CandidateGraph as Graph
import Mimir.EmbeddingLifecycle as Lifecycle
import Mimir.PublicEncoding as Encoding
import Mimir.RetrievalRanking as Ranking
import Mimir.StructuredValue as Wire
import Mimir.Recovery as Recovery
import Mimir.DatabaseTransaction as DB
import Mimir.RecoverableStoreStep as StoreStep
import Mimir.OperationControls as Controls
import Mimir.StandardLibrary as Library
import Mimir.RegisteredStoreAdmission as Registered
import Mimir.ProjectDeletion as Project
import Mimir.Validation as Validation
open import Data.String using (toList)
open import Relation.Nullary using (yes; no)

record Source : Set where
  constructor source
  field
    identity : ℕ
    content : Text
    project : Maybe Text
    alreadyEmbedded : Bool

before : Graph.BeliefValues → Graph.BeliefValues → Bool
before first second = does (Graph.BeliefValues.identity first ≤? Graph.BeliefValues.identity second)

capture : Store.World → List Source
capture snapshot = map fromBelief (Ranking.sort before (Store.beliefs snapshot))
  where
  fromBelief : Graph.BeliefValues → Source
  fromBelief belief = source (Graph.BeliefValues.identity belief)
    (Graph.BeliefValues.content belief) (Graph.BeliefValues.project belief)
    (Ranking.member (Graph.BeliefValues.identity belief)
      (map proj₁ (Store.World.beliefVectors snapshot)))

pending : List Source → List Source
pending = filterᵇ (λ item → not (Source.alreadyEmbedded item))

initiallySkipped : List Source → ℕ
initiallySkipped rows = length (filterᵇ Source.alreadyEmbedded rows)

module Encode (format : Encoding.Formatting) where
  module E = Encoding.Encode format

  row : Source → Wire.Value
  row item = Encoding.object
    (("id" , E.uuid (Source.identity item)) ∷
     ("content" , Wire.string (Source.content item)) ∷
     ("project" , Encoding.optional Wire.string (Source.project item)) ∷
     ("already_embedded" , Wire.boolean (Source.alreadyEmbedded item)) ∷ [])

  snapshot : List Source → Wire.Value
  snapshot rows = Encoding.object (("beliefs" , Wire.array (map row rows)) ∷ [])

-- These are observations, not a choice to overwrite, skip or cancel. The
-- operation must separately apply the agreed policy to each observed state.
data Current : Set where
  missing changed alreadyPresent pendingVector : Current

current : Source → Store.World → Current
current expected snapshot with Ranking.lookup (Source.identity expected) (Store.beliefs snapshot)
... | nothing = missing
... | just belief with does (Source.content expected ≟Text Graph.BeliefValues.content belief) ∧
  does (Maybes.≡-dec _≟Text_ (Source.project expected) (Graph.BeliefValues.project belief))
... | false = changed
... | true with Ranking.member (Source.identity expected) (map proj₁ (Store.World.beliefVectors snapshot))
... | true = alreadyPresent
... | false = pendingVector

active : ℕ → Graph.BeliefValues → Store.World → Bool
active token belief snapshot with Store.lookupCancellation snapshot token
... | just _ = false
... | nothing = Backfill.ownsBackfill belief snapshot

checkedOwnership : ℕ → Graph.BeliefValues → Store.World → Lifecycle.Ownership.State → Lifecycle.Ownership.State
checkedOwnership token belief snapshot owned with active token belief snapshot
... | true = owned
... | false = Lifecycle.Ownership.stop owned

cancelledOperationStopsItsJob : ∀ token belief snapshot owned cancelled →
  Store.lookupCancellation snapshot token ≡ just cancelled →
  checkedOwnership token belief snapshot owned ≡ Lifecycle.Ownership.stop owned
cancelledOperationStopsItsJob token belief snapshot owned cancelled recorded rewrite recorded = refl

-- The user-approved concurrency rule is checked again under the publication
-- lock. A provider reply cannot authorize overwriting another completed vector
-- or writing an embedding for changed/deleted source text.
data Decision : Set where
  askUser skipExisting prepareVector : Decision

decision : Source → Store.World → Decision
decision expected snapshot with current expected snapshot
... | missing = askUser
... | changed = askUser
... | alreadyPresent = skipExisting
... | pendingVector = prepareVector

data ItemResult : Set where
  dialogue : ItemResult
  skipped embedded : ItemResult

-- This describes the business outcome, independently of journal publication.
-- The vector is an observed preparation result, never an invocation argument.
itemIntent : Source → Maybe Store.Vector → Store.World → Store.World × ItemResult
itemIntent expected observed before with decision expected before
... | askUser = before , dialogue
... | skipExisting = before , skipped
... | prepareVector with observed
... | nothing = before , dialogue
... | just vector with Backfill.usableVector vector
... | false = before , dialogue
... | true = record before
  { beliefVectors = (Source.identity expected , vector) ∷ Store.World.beliefVectors before } , embedded

existingVectorIsPreserved : ∀ expected observed before →
  decision expected before ≡ skipExisting → itemIntent expected observed before ≡ (before , skipped)
existingVectorIsPreserved expected observed before same rewrite same = refl

changedSourceCannotPublish : ∀ expected observed before →
  decision expected before ≡ askUser → itemIntent expected observed before ≡ (before , dialogue)
changedSourceCannotPublish expected observed before same rewrite same = refl

unavailablePreparationCannotCountEmbedded : ∀ expected before →
  decision expected before ≡ prepareVector → itemIntent expected nothing before ≡ (before , dialogue)
unavailablePreparationCannotCountEmbedded expected before same rewrite same = refl

checkedDecisionOwnership : Decision → Lifecycle.Ownership.State → Lifecycle.Ownership.State
checkedDecisionOwnership prepareVector owned = owned
checkedDecisionOwnership _ owned = Lifecycle.Ownership.stop owned

stopsRedundantJob : ∀ expected before owned → decision expected before ≡ skipExisting →
  checkedDecisionOwnership (decision expected before) owned ≡ Lifecycle.Ownership.stop owned
stopsRedundantJob expected before owned same rewrite same = refl

completeSource : Source → Store.World → Bool
completeSource expected before with current expected before
... | alreadyPresent = true
... | _ = false

completeSelection : List Source → Store.World → Bool
completeSelection [] before = true
completeSelection (first ∷ rest) before = completeSource first before ∧ completeSelection rest before

everySelectedSourceComplete : ∀ selected before → completeSelection selected before ≡ true →
  All (λ source → completeSource source before ≡ true) selected
everySelectedSourceComplete [] before complete = []
everySelectedSourceComplete (first ∷ rest) before complete with completeSource first before in observed
... | false with complete
... | ()
everySelectedSourceComplete (first ∷ rest) before complete | true =
  observed ∷ everySelectedSourceComplete rest before complete

-- The final publication makes a claim about ALL original sources, including
-- initially skipped rows and the saved prefix. A lost prior vector cannot be
-- hidden by an immutable acknowledgement or by a successful final item.
finalItemIntent : List Source → Source → Maybe Store.Vector → Store.World → Store.World × ItemResult
finalItemIntent selected last observed before with itemIntent last observed before
... | candidate , dialogue = before , dialogue
... | candidate , skipped with completeSelection selected candidate
... | true = candidate , skipped
... | false = before , dialogue
finalItemIntent selected last observed before | candidate , embedded with completeSelection selected candidate
... | true = candidate , embedded
... | false = before , dialogue

finalSkipRequiresCompleteSelection : ∀ selected last observed before after →
  finalItemIntent selected last observed before ≡ (after , skipped) →
  All (λ source → completeSource source after ≡ true) selected
finalSkipRequiresCompleteSelection selected last observed before after accepted with itemIntent last observed before
... | candidate , dialogue with accepted
... | ()
finalSkipRequiresCompleteSelection selected last observed before after accepted | candidate , skipped
  with completeSelection selected candidate in complete
... | false with accepted
... | ()
finalSkipRequiresCompleteSelection selected last observed before after accepted | candidate , skipped | true with accepted
... | refl = everySelectedSourceComplete selected candidate complete
finalSkipRequiresCompleteSelection selected last observed before after accepted | candidate , embedded
  with completeSelection selected candidate
... | false with accepted
... | ()
finalSkipRequiresCompleteSelection selected last observed before after accepted | candidate , embedded | true with accepted
... | ()

finalEmbeddingRequiresCompleteSelection : ∀ selected last observed before after →
  finalItemIntent selected last observed before ≡ (after , embedded) →
  All (λ source → completeSource source after ≡ true) selected
finalEmbeddingRequiresCompleteSelection selected last observed before after accepted with itemIntent last observed before
... | candidate , dialogue with accepted
... | ()
finalEmbeddingRequiresCompleteSelection selected last observed before after accepted | candidate , skipped
  with completeSelection selected candidate
... | false with accepted
... | ()
finalEmbeddingRequiresCompleteSelection selected last observed before after accepted | candidate , skipped | true with accepted
... | ()
finalEmbeddingRequiresCompleteSelection selected last observed before after accepted | candidate , embedded
  with completeSelection selected candidate in complete
... | false with accepted
... | ()
finalEmbeddingRequiresCompleteSelection selected last observed before after accepted | candidate , embedded | true with accepted
... | refl = everySelectedSourceComplete selected candidate complete

-- The frame accounts for the complete World. Only vector rows and this
-- operation's receipt rows may be added; every other represented field is
-- retained, including cancellations, plans, provenance and graph counts.
restOfWorld : Store.World → Store.World
restOfWorld before = record before
  { beliefVectors = []
  ; operations = record (Store.World.operations before) { savedReplies = [] } }

sourceMatches : Source → Store.World → Bool
sourceMatches expected before with current expected (record before { beliefVectors = [] })
... | pendingVector = true
... | _ = false

data Contains (expected : Source) : List Source → Set where
  containsHere : ∀ rest → Contains expected (expected ∷ rest)
  containsThere : ∀ source rest → Contains expected rest → Contains expected (source ∷ rest)

memberText : Text → List Text → Bool
memberText key [] = false
memberText key (first ∷ rest) = does (key ≟Text first) ∨ memberText key rest

-- This describes permitted final vector data, not an execution transcript or
-- a sequence of SQL statements. In particular it forbids replacing an old
-- vector and forbids introducing an unusable or unrelated vector.
data VectorExtension (selected : List Source) (original : Store.World) :
  List (ℕ × Store.Vector) → List (ℕ × Store.Vector) → Set where
  originalVectors : ∀ rows → VectorExtension selected original rows rows
  addedVector : ∀ old current source vector →
    Contains source selected → sourceMatches source original ≡ true →
    Backfill.usableVector vector ≡ true →
    Ranking.member (Source.identity source) (map proj₁ current) ≡ false →
    VectorExtension selected original old current →
    VectorExtension selected original old ((Source.identity source , vector) ∷ current)

data ReplyExtension (token : ℕ) (keys : List Text) :
  List Store.SavedReplyRow → List Store.SavedReplyRow → Set where
  originalReplies : ∀ rows → ReplyExtension token keys rows rows
  addedReply : ∀ old current key value →
    memberText key keys ≡ true →
    Store.lookupReply token key current ≡ nothing →
    ReplyExtension token keys old current →
    ReplyExtension token keys old (Store.savedReplyRow token key value ∷ current)

record Frame (token : ℕ) (keys : List Text) (selected : List Source)
  (original final : Store.World) : Set where
  field
    otherFields : restOfWorld final ≡ restOfWorld original
    vectorRows : VectorExtension selected original
      (Store.World.beliefVectors original) (Store.World.beliefVectors final)
    receiptRows : ReplyExtension token keys
      (Store.OperationTables.savedReplies (Store.World.operations original))
      (Store.OperationTables.savedReplies (Store.World.operations final))

initialFrame : ∀ token keys selected original → Frame token keys selected original original
initialFrame token keys selected original = record
  { otherFields = refl; vectorRows = originalVectors _; receiptRows = originalReplies _ }

-- This is the server's private plan capability. The rows are decoded from the
-- stored capture; they are not extra fields accepted from an agent request.
module Admission (library : Library.Contract) where
  module Plan = Controls.Plan

  mismatch : Validation.Fault
  mismatch = Validation.fault [] Validation.wrongIdentity
    "Read the original reembed binding, saved capture and item answers. Ask the user to resolve missing or changed metadata; do not replace the selection or model."

  record Context : Set where
    constructor context
    field token : ℕ
          binding : Store.BindingRow
          rawPlan : Wire.Value
          plan : Plan.Saved
          rawCapture : Wire.Value
          rows : List Plan.CapturedSource
          decodedPlan : Plan.decode rawPlan ≡ inj₂ plan
          validPlan : Plan.valid library plan ≡ true
          captured : Plan.Saved.capture plan ≡ just rawCapture
          decodedCapture : Plan.readCapture library rawCapture ≡ inj₂ rows

  provider : Wire.Value → Bool
  provider raw = Project.Registered.fields (toList "embeddings" ∷ []) (λ view →
    caseEmbedding (view (toList "embeddings"))) raw
    where
    identity : Wire.Value → Bool
    identity raw =
      Project.Registered.fields (toList "backend" ∷ toList "model" ∷ [])
        (λ view → Project.Registered.fieldText (toList "local") (view (toList "backend")) ∧
          Project.Registered.fieldText (toList "BAAI/bge-base-en-v1.5") (view (toList "model"))) raw ∨
      Project.Registered.fields (toList "backend" ∷ toList "model" ∷ [])
        (λ view → Project.Registered.fieldText (toList "openai") (view (toList "backend")) ∧
          stringField (view (toList "model"))) raw ∨
      Project.Registered.fields (toList "backend" ∷ toList "model" ∷ toList "input_type" ∷ toList "truncation" ∷ [])
        (λ view → Project.Registered.fieldText (toList "voyage") (view (toList "backend")) ∧
          stringField (view (toList "model")) ∧
          Project.Registered.fieldText (toList "document") (view (toList "input_type")) ∧
          Project.Registered.fieldFalse (view (toList "truncation"))) raw
      where
      stringField : Maybe Wire.Value → Bool
      stringField (just (Wire.string _)) = true
      stringField _ = false

    caseEmbedding : Maybe Wire.Value → Bool
    caseEmbedding (just Wire.null) = true
    caseEmbedding (just raw) = identity raw
    caseEmbedding nothing = false

  original : ℕ → StoreStep.Registration → Validation.Fault ⊎ Context
  original token registration with Registered.originalPlan (toList "reembed") token registration
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ (reserved , binding , raw) with Store.BindingRow.arguments binding | provider (Store.BindingRow.settings binding)
  ... | Wire.object [] | true with Plan.decode raw in decoded
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ plan with Plan.valid library plan in valid
  ... | false = inj₁ mismatch
  ... | true with Plan.Saved.capture plan in captured
  ... | nothing = inj₁ mismatch
  ... | just capture with Plan.readCapture library capture in sourceRows
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ rows = inj₂ (context token binding raw plan capture rows decoded valid captured sourceRows)
  original token registration | inj₂ (reserved , binding , raw) | _ | _ = inj₁ mismatch

  semanticSource : Plan.CapturedSource → Source
  semanticSource row = source (Plan.CapturedSource.identity row) (Plan.CapturedSource.content row)
    (Plan.CapturedSource.project row) (Plan.CapturedSource.alreadyEmbedded row)

  selected : Context → List Source
  selected current = map semanticSource (Context.rows current)

  keys : Context → List Text
  keys current = StoreStep.resultKey ∷ map Plan.Step.id (Plan.Saved.steps (Context.plan current))
