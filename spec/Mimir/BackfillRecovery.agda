{-# OPTIONS --safe #-}
-- A backfill keeps its original source selection and truthful original counts.
-- Preparation is observed work; no caller supplies an expected vector/result.
module Mimir.BackfillRecovery where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.List using (List; []; _∷_; _++_; map; filterᵇ; length; null)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Properties as Maybes
open import Data.Nat using (ℕ; _≤?_; suc; _+_; _≟_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
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
import Data.List.Properties as Lists
import Data.Fin.Properties as Fin
open import Mimir.Bits using (Byte)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
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

currentView : Source → List Graph.BeliefValues → List ℕ → Current
currentView expected beliefs vectors with Ranking.lookup (Source.identity expected) beliefs
... | nothing = missing
... | just belief with does (Source.content expected ≟Text Graph.BeliefValues.content belief) ∧
  does (Maybes.≡-dec _≟Text_ (Source.project expected) (Graph.BeliefValues.project belief))
... | false = changed
... | true with Ranking.member (Source.identity expected) vectors
... | true = alreadyPresent
... | false = pendingVector

current : Source → Store.World → Current
current expected snapshot = currentView expected (Store.beliefs snapshot)
  (map proj₁ (Store.World.beliefVectors snapshot))

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

completeCurrent : Current → Bool
completeCurrent alreadyPresent = true
completeCurrent _ = false

completeSource : Source → Store.World → Bool
completeSource expected before = completeCurrent (current expected before)

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

allSelectedImpliesComplete : ∀ selected before →
  All (λ source → completeSource source before ≡ true) selected → completeSelection selected before ≡ true
allSelectedImpliesComplete [] before [] = refl
allSelectedImpliesComplete (expected ∷ rest) before (firstComplete ∷ restComplete)
  rewrite firstComplete | allSelectedImpliesComplete rest before restComplete = refl

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

Successful : ItemResult → Set
Successful dialogue = ⊥
Successful skipped = ⊤
Successful embedded = ⊤

finalIntentComplete : ∀ selected expected packet before candidate result → Successful result →
  finalItemIntent selected expected packet before ≡ (candidate , result) → completeSelection selected candidate ≡ true
finalIntentComplete selected expected packet before candidate dialogue () accepted
finalIntentComplete selected expected packet before candidate skipped successful accepted =
  allSelectedImpliesComplete selected candidate
    (finalSkipRequiresCompleteSelection selected expected packet before candidate accepted)
finalIntentComplete selected expected packet before candidate embedded successful accepted =
  allSelectedImpliesComplete selected candidate
    (finalEmbeddingRequiresCompleteSelection selected expected packet before candidate accepted)

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

data Contains {A : Set} (expected : A) : List A → Set where
  containsHere : ∀ rest → Contains expected (expected ∷ rest)
  containsThere : ∀ source rest → Contains expected rest → Contains expected (source ∷ rest)

memberText : Text → List Text → Bool
memberText key [] = false
memberText key (first ∷ rest) = does (key ≟Text first) ∨ memberText key rest

memberTextHead : ∀ key rest → memberText key (key ∷ rest) ≡ true
memberTextHead key rest with key ≟Text key
... | yes _ = refl
... | no impossible = ⊥-elim (impossible refl)

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

-- Selection/model admission only reads the immutable reservation, binding
-- and plan components. Item publication cannot reinterpret those components.
frameKeepsRegistration : ∀ token keys selected original final → Frame token keys selected original final →
  StoreStep.registration final ≡ StoreStep.registration original
frameKeepsRegistration token keys selected original final frame =
  cong StoreStep.registration (Frame.otherFields frame)

initialFrame : ∀ token keys selected original → Frame token keys selected original original
initialFrame token keys selected original = record
  { otherFields = refl; vectorRows = originalVectors _; receiptRows = originalReplies _ }

mapContains : ∀ {A B : Set} (f : A → B) {value rows} → Contains value rows → Contains (f value) (map f rows)
mapContains f (containsHere rest) = containsHere (map f rest)
mapContains f (containsThere value rest member) = containsThere (f value) (map f rest) (mapContains f member)

memberTextTail : ∀ key first rest → memberText key rest ≡ true → memberText key (first ∷ rest) ≡ true
memberTextTail key first rest member with does (key ≟Text first)
... | true = refl
... | false = member

mappedTextMember : ∀ {A : Set} (f : A → Text) {value rows} →
  Contains value rows → memberText (f value) (map f rows) ≡ true
mappedTextMember f {value = value} (containsHere rest) with f value ≟Text f value
... | yes _ = refl
... | no impossible = ⊥-elim (impossible refl)
mappedTextMember f (containsThere value rest member) =
  memberTextTail _ (f value) (map f rest) (mappedTextMember f member)

savingAnswerKeepsFrame : ∀ token keys selected original before key value →
  memberText key keys ≡ true → Frame token keys selected original before →
  Frame token keys selected original (Store.saveAnswer before token key value)
savingAnswerKeepsFrame token keys selected original before key value owns prior
  with Store.lookupSaved before token key in saved
... | just _ = prior
... | nothing = record
  { otherFields = Frame.otherFields prior
  ; vectorRows = Frame.vectorRows prior
  ; receiptRows = addedReply _ _ key value owns saved (Frame.receiptRows prior) }

savingMissingAnswerReadable : ∀ before token key value → Store.lookupSaved before token key ≡ nothing →
  Store.lookupSaved (Store.saveAnswer before token key value) token key ≡ just value
savingMissingAnswerReadable before token key value absent rewrite absent =
  Store.headReplyReadable token key value (Store.OperationTables.savedReplies (Store.World.operations before))

addingVectorKeepsFrame : ∀ token keys selected original before expected vector →
  Contains expected selected → sourceMatches expected before ≡ true →
  Backfill.usableVector vector ≡ true →
  Ranking.member (Source.identity expected) (map proj₁ (Store.World.beliefVectors before)) ≡ false →
  Frame token keys selected original before →
  Frame token keys selected original (record before
    { beliefVectors = (Source.identity expected , vector) ∷ Store.World.beliefVectors before })
addingVectorKeepsFrame token keys selected original before expected vector owns matching valid absent prior = record
  { otherFields = Frame.otherFields prior
  ; vectorRows = addedVector _ _ expected vector owns
      (trans (sym (cong (sourceMatches expected) (Frame.otherFields prior))) matching)
      valid absent (Frame.vectorRows prior)
  ; receiptRows = Frame.receiptRows prior }

pendingSourceFacts : ∀ expected before → current expected before ≡ pendingVector →
  sourceMatches expected before ≡ true ×
  Ranking.member (Source.identity expected) (map proj₁ (Store.World.beliefVectors before)) ≡ false
pendingSourceFacts expected before pending with Ranking.lookup (Source.identity expected) (Store.beliefs before) in found
... | nothing with pending
... | ()
pendingSourceFacts expected before pending | just belief with
  does (Source.content expected ≟Text Graph.BeliefValues.content belief) ∧
  does (Maybes.≡-dec _≟Text_ (Source.project expected) (Graph.BeliefValues.project belief)) in matching
... | false with pending
... | ()
pendingSourceFacts expected before pending | just belief | true with
  Ranking.member (Source.identity expected) (map proj₁ (Store.World.beliefVectors before)) in present
... | true with pending
... | ()
pendingSourceFacts expected before pending | just belief | true | false = refl , refl

itemIntentKeepsFrame : ∀ token keys selected original before expected packet →
  Contains expected selected → Frame token keys selected original before →
  Frame token keys selected original (proj₁ (itemIntent expected packet before))
itemIntentKeepsFrame token keys selected original before expected packet owns prior
  with current expected before in state
... | missing = prior
... | changed = prior
... | alreadyPresent = prior
... | pendingVector with packet
... | nothing = prior
... | just vector with Backfill.usableVector vector in valid
... | false = prior
... | true = addingVectorKeepsFrame token keys selected original before expected vector owns
  (proj₁ (pendingSourceFacts expected before state)) valid
  (proj₂ (pendingSourceFacts expected before state)) prior

finalIntentKeepsFrame : ∀ token keys selected original before expected packet →
  Contains expected selected → Frame token keys selected original before →
  Frame token keys selected original (proj₁ (finalItemIntent selected expected packet before))
finalIntentKeepsFrame token keys selected original before expected packet owns prior
  with itemIntent expected packet before | itemIntentKeepsFrame token keys selected original before expected packet owns prior
... | candidate , dialogue | candidateFrame = prior
... | candidate , skipped | candidateFrame with completeSelection selected candidate
... | false = prior
... | true = candidateFrame
finalIntentKeepsFrame token keys selected original before expected packet owns prior
  | candidate , embedded | candidateFrame with completeSelection selected candidate
... | false = prior
... | true = candidateFrame

itemIntentKeepsOperations : ∀ expected packet before →
  Store.World.operations (proj₁ (itemIntent expected packet before)) ≡ Store.World.operations before
itemIntentKeepsOperations expected packet before with decision expected before
... | askUser = refl
... | skipExisting = refl
... | prepareVector with packet
... | nothing = refl
... | just vector with Backfill.usableVector vector
... | false = refl
... | true = refl

finalIntentKeepsOperations : ∀ selected expected packet before →
  Store.World.operations (proj₁ (finalItemIntent selected expected packet before)) ≡ Store.World.operations before
finalIntentKeepsOperations selected expected packet before with itemIntent expected packet before |
  itemIntentKeepsOperations expected packet before
... | candidate , dialogue | kept = refl
... | candidate , skipped | kept with completeSelection selected candidate
... | false = refl
... | true = kept
finalIntentKeepsOperations selected expected packet before | candidate , embedded | kept with completeSelection selected candidate
... | false = refl
... | true = kept

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

  -- Keep observations explicit so assembly can transport successful actual
  -- decoder receipts without assuming equality between arbitrary proof fields.
  afterSources : ∀ token binding raw plan capture →
    Plan.decode raw ≡ inj₂ plan → Plan.valid library plan ≡ true →
    Plan.Saved.capture plan ≡ just capture →
    (observed : Validation.Fault ⊎ List Plan.CapturedSource) →
    Plan.readCapture library capture ≡ observed → Validation.Fault ⊎ Context
  afterSources token binding raw plan capture decoded valid captured (inj₁ fault) observed = inj₁ fault
  afterSources token binding raw plan capture decoded valid captured (inj₂ rows) observed =
    inj₂ (context token binding raw plan capture rows decoded valid captured observed)

  afterCapture : ∀ token binding raw plan →
    Plan.decode raw ≡ inj₂ plan → Plan.valid library plan ≡ true →
    (observed : Maybe Wire.Value) → Plan.Saved.capture plan ≡ observed → Validation.Fault ⊎ Context
  afterCapture token binding raw plan decoded valid nothing captured = inj₁ mismatch
  afterCapture token binding raw plan decoded valid (just capture) captured =
    afterSources token binding raw plan capture decoded valid captured (Plan.readCapture library capture) refl

  afterValid : ∀ token binding raw plan → Plan.decode raw ≡ inj₂ plan →
    (observed : Bool) → Plan.valid library plan ≡ observed → Validation.Fault ⊎ Context
  afterValid token binding raw plan decoded false valid = inj₁ mismatch
  afterValid token binding raw plan decoded true valid =
    afterCapture token binding raw plan decoded valid (Plan.Saved.capture plan) refl

  afterDecode : ∀ token binding raw → (observed : Validation.Fault ⊎ Plan.Saved) →
    Plan.decode raw ≡ observed → Validation.Fault ⊎ Context
  afterDecode token binding raw (inj₁ fault) decoded = inj₁ fault
  afterDecode token binding raw (inj₂ plan) decoded =
    afterValid token binding raw plan decoded (Plan.valid library plan) refl

  original : ℕ → StoreStep.Registration → Validation.Fault ⊎ Context
  original token registration with Registered.originalPlan (toList "reembed") token registration
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ (reserved , binding , raw) with Store.BindingRow.arguments binding | provider (Store.BindingRow.settings binding)
  ... | Wire.object [] | true = afterDecode token binding raw (Plan.decode raw) refl
  ... | _ | _ = inj₁ mismatch

  semanticSource : Plan.CapturedSource → Source
  semanticSource row = source (Plan.CapturedSource.identity row) (Plan.CapturedSource.content row)
    (Plan.CapturedSource.project row) (Plan.CapturedSource.alreadyEmbedded row)

  selected : Context → List Source
  selected current = map semanticSource (Context.rows current)

  keys : Context → List Text
  keys current = StoreStep.resultKey ∷ map Plan.Step.id (Plan.Saved.steps (Context.plan current))

  signature : Context → Wire.Value
  signature current = Wire.array
    (Wire.string (Store.BindingRow.operation binding) ∷ Store.BindingRow.arguments binding ∷
     Store.BindingRow.settings binding ∷ Context.rawPlan current ∷ [])
    where binding = Context.binding current

  admit : Context → Store.World → Maybe Validation.Fault
  admit expected before with original (Context.token expected) (StoreStep.registration before)
  ... | inj₁ fault = just fault
  ... | inj₂ current with Lists.≡-dec Fin._≟_
    (Library.Contract.compactJSON library (signature expected))
    (Library.Contract.compactJSON library (signature current))
  ... | yes _ = nothing
  ... | no _ = just mismatch

-- Existing standard-library correspondence: an item key is a JSON array;
-- the reserved result key is a different constructor. No encoder is proved.
itemKey : Library.Contract → Controls.Plan.CapturedSource → Text
itemKey library row = Controls.Plan.Step.id (Controls.Plan.canonicalStep library
  (toList "store.insert_belief_embedding") (just (Controls.Plan.CapturedSource.id row)))

record JournalEncoding (library : Library.Contract) : Set where
  field itemIsNotResult : ∀ row → itemKey library row ≡ StoreStep.resultKey → ⊥
        declaredIsNotResult : ∀ plan → Controls.Plan.valid library plan ≡ true →
          ∀ statement → Contains statement (Controls.Plan.Saved.steps plan) →
          Controls.Plan.Step.id statement ≡ StoreStep.resultKey → ⊥

intentForFinal : Bool → List Source → Source → Maybe Store.Vector → Store.World → Store.World × ItemResult
intentForFinal true = finalItemIntent
intentForFinal false _ = itemIntent

intentKeepsFrame : ∀ final token keys selected original before expected packet →
  Contains expected selected → Frame token keys selected original before →
  Frame token keys selected original (proj₁ (intentForFinal final selected expected packet before))
intentKeepsFrame true = finalIntentKeepsFrame
intentKeepsFrame false = itemIntentKeepsFrame

intentKeepsOperations : ∀ final selected expected packet before →
  Store.World.operations (proj₁ (intentForFinal final selected expected packet before)) ≡ Store.World.operations before
intentKeepsOperations true = finalIntentKeepsOperations
intentKeepsOperations false selected = itemIntentKeepsOperations

-- A successful item outcome is tied to the real source/vector observation.
data ItemMeaning (expected : Source) (before : Store.World) : Store.World → ItemResult → Set where
  preservedVector : current expected before ≡ alreadyPresent → ItemMeaning expected before before skipped
  publishedVector : ∀ vector → current expected before ≡ pendingVector → Backfill.usableVector vector ≡ true →
    ItemMeaning expected before
      (record before { beliefVectors = (Source.identity expected , vector) ∷ Store.World.beliefVectors before }) embedded

itemSuccessMeaning : ∀ expected packet before candidate result → Successful result →
  itemIntent expected packet before ≡ (candidate , result) → ItemMeaning expected before candidate result
itemSuccessMeaning expected packet before candidate result successful accepted with current expected before in seen
... | missing with accepted
... | refl with successful
... | ()
itemSuccessMeaning expected packet before candidate result successful accepted | changed with accepted
... | refl with successful
... | ()
itemSuccessMeaning expected packet before candidate result successful accepted | alreadyPresent with accepted
... | refl = preservedVector seen
itemSuccessMeaning expected packet before candidate result successful accepted | pendingVector with packet
... | nothing with accepted
... | refl with successful
... | ()
itemSuccessMeaning expected packet before candidate result successful accepted | pendingVector | just vector
  with Backfill.usableVector vector in usable
... | false with accepted
... | refl with successful
... | ()
itemSuccessMeaning expected packet before candidate result successful accepted | pendingVector | just vector | true with accepted
... | refl = publishedVector vector seen usable

intentSuccessMeaning : ∀ final selected expected packet before candidate result → Successful result →
  intentForFinal final selected expected packet before ≡ (candidate , result) → ItemMeaning expected before candidate result
intentSuccessMeaning false selected = itemSuccessMeaning
intentSuccessMeaning true selected expected packet before candidate result successful accepted
  with itemIntent expected packet before in item
... | next , dialogue with accepted
... | refl with successful
... | ()
intentSuccessMeaning true selected expected packet before candidate result successful accepted | next , skipped
  with completeSelection selected next
... | false with accepted
... | refl with successful
... | ()
intentSuccessMeaning true selected expected packet before candidate result successful accepted | next , skipped | true with accepted
... | refl = itemSuccessMeaning expected packet before next skipped tt item
intentSuccessMeaning true selected expected packet before candidate result successful accepted | next , embedded
  with completeSelection selected next
... | false with accepted
... | refl with successful
... | ()
intentSuccessMeaning true selected expected packet before candidate result successful accepted | next , embedded | true with accepted
... | refl = itemSuccessMeaning expected packet before next embedded tt item

module Body (library : Library.Contract) (postgres : Controls.PostgreSQL)
  (encoding : JournalEncoding library)
  (context : Admission.Context library) where
  module A = Admission library
  module Plan = Controls.Plan
  module Read = Controls.Readback library postgres

  token = A.Context.token context
  selected = A.selected context
  keys = A.keys context

  rowKey : Plan.CapturedSource → Text
  rowKey row = Plan.Step.id (Plan.canonicalStep library (toList "store.insert_belief_embedding")
    (just (Plan.CapturedSource.id row)))

  record Counts : Set where
    constructor counts
    field embeddedCount skippedCount : ℕ

  status : Wire.Value → Maybe Bool
  status raw with Project.Registered.fields (toList "status" ∷ [])
    (λ view → Project.Registered.fieldText (toList "embedded") (view (toList "status"))) raw
  ... | true = just true
  ... | false with Project.Registered.fields (toList "status" ∷ [])
    (λ view → Project.Registered.fieldText (toList "skipped") (view (toList "status"))) raw
  ... | true = just false
  ... | false = nothing

  countRows : List Plan.CapturedSource → Store.World → Maybe Counts
  countRows [] before = just (counts 0 0)
  countRows (row ∷ rest) before with countRows rest before
  ... | nothing = nothing
  ... | just remaining with Plan.CapturedSource.alreadyEmbedded row
  ... | true = just (record remaining { skippedCount = suc (Counts.skippedCount remaining) })
  ... | false with Store.lookupSaved before token (rowKey row)
  ... | nothing = nothing
  ... | just raw with status raw
  ... | nothing = nothing
  ... | just true = just (record remaining { embeddedCount = suc (Counts.embeddedCount remaining) })
  ... | just false = just (record remaining { skippedCount = suc (Counts.skippedCount remaining) })

  encodedCounts : Counts → Wire.Value
  encodedCounts current = Encoding.object
    (("embedded" , Wire.unsigned (Counts.embeddedCount current)) ∷
     ("skipped" , Wire.unsigned (Counts.skippedCount current)) ∷ [])

  encodedItem : ItemResult → Wire.Value
  encodedItem embedded = Encoding.object (("status" , Wire.string (toList "embedded")) ∷ [])
  encodedItem skipped = Encoding.object (("status" , Wire.string (toList "skipped")) ∷ [])
  encodedItem dialogue = Wire.null

  readySource : Plan.CapturedSource → Store.World → Bool
  readySource row before with current (A.semanticSource row) before
  ... | missing = false
  ... | changed = false
  ... | alreadyPresent = true
  ... | pendingVector with Plan.CapturedSource.alreadyEmbedded row | Store.lookupSaved before token (rowKey row)
  ... | false | nothing = true
  ... | _ | _ = false

  readySelection : List Plan.CapturedSource → Store.World → Bool
  readySelection [] before = true
  readySelection (row ∷ rest) before = readySource row before ∧ readySelection rest before

  stale : Validation.Fault
  stale = Validation.fault [] Validation.staleRevision
    "An original source changed, was deleted, or lost an already counted vector. Read the original capture and saved answers and open a user dialog. Do not restart old provider work or rewrite its immutable answers."

  preparationMissing : Validation.Fault
  preparationMissing = Validation.fault (Validation.key "embeddings" ∷ []) Validation.missingEvidence
    "No usable embedding was prepared for the original complete source and model. Open a user dialog to repair the backend or cancel; no item answer or vector was committed."

  data View : Set where
    ready : View
    terminal : StoreStep.Result Validation.Fault → View

  existingView : Wire.Value → Read.Result → StoreStep.Result Validation.Fault
  existingView saved (Read.completed _ _) = StoreStep.done saved
  existingView saved (Read.cancelled cancellation _ _) = StoreStep.cancelled cancellation
  existingView saved _ = StoreStep.needsRecovery

  unfinishedView : Read.Result → View
  unfinishedView (Read.pending _ _ _) = ready
  unfinishedView (Read.awaitingCompletion _) = ready
  unfinishedView (Read.cancelled cancellation _ _) = terminal (StoreStep.cancelled cancellation)
  unfinishedView _ = terminal StoreStep.needsRecovery

  inspect : Store.World → View
  inspect before with A.admit context before
  ... | just fault = terminal (StoreStep.needsInput fault)
  ... | nothing with Store.lookupSaved before token StoreStep.resultKey
  ... | just saved = terminal (existingView saved (Read.answer token before))
  ... | nothing = unfinishedView (Read.answer token before)

  record Found (key : Text) : Set where
    constructor found
    field row : Plan.CapturedSource
          member : Contains row (A.Context.rows context)

  findSourceIn : ∀ key rows → Maybe (Σ Plan.CapturedSource (λ row → Contains row rows))
  findSourceIn key [] = nothing
  findSourceIn key (row ∷ rest) with key ≟Text Plan.CapturedSource.id row
  ... | yes _ with Plan.CapturedSource.alreadyEmbedded row
  ... | false = just (row , containsHere rest)
  ... | true = nothing
  findSourceIn key (row ∷ rest) | no _ with findSourceIn key rest
  ... | nothing = nothing
  ... | just (selected , member) = just (selected , containsThere row rest member)

  findSource : Maybe Text → Maybe Plan.CapturedSource
  findSource nothing = nothing
  findSource (just key) with findSourceIn key (A.Context.rows context)
  ... | nothing = nothing
  ... | just (row , member) = just row

  -- Internal observation of the actual owned invocation, not extra request
  -- fields and not a promise that a vendor's numeric vector is deterministic.
  record PreparedPacket : Set where
    constructor preparedPacket
    field owner identity : ℕ
          content : Text
          project : Maybe Text
          settings : Wire.Value
          vector : Store.Vector

  data Preparation : Set where
    unavailable : Text → Preparation
    observed : PreparedPacket → Preparation
    superseded : Preparation

  packetScope : Plan.CapturedSource → PreparedPacket → Bool
  packetScope row packet = does (PreparedPacket.owner packet ≟ token) ∧
    does (PreparedPacket.identity packet ≟ Plan.CapturedSource.identity row) ∧
    does (PreparedPacket.content packet ≟Text Plan.CapturedSource.content row) ∧
    does (Maybes.≡-dec _≟Text_ (PreparedPacket.project packet) (Plan.CapturedSource.project row)) ∧
    does (Lists.≡-dec Fin._≟_ (Library.Contract.compactJSON library (PreparedPacket.settings packet))
      (Library.Contract.compactJSON library (Store.BindingRow.settings (A.Context.binding context))))

  preparedVector : Plan.CapturedSource → Preparation → Maybe Store.Vector
  preparedVector row (observed packet) with packetScope row packet
  ... | true = just (PreparedPacket.vector packet)
  ... | false = nothing
  preparedVector row _ = nothing

  preparationFault : Preparation → Validation.Fault
  preparationFault (unavailable cause) = record preparationMissing
    { explanation = Validation.Fault.explanation preparationMissing ++ cause }
  preparationFault _ = preparationMissing

  record Proposal (before : Store.World) : Set where
    constructor proposal
    field publicationWorld : Store.World
          returned : StoreStep.Result Validation.Fault
          physical : DB.Atomic before publicationWorld (StoreStep.receiptFor returned) publicationWorld

  committed : ∀ before after → Wire.Value → Proposal before
  committed before after value = proposal after (StoreStep.done value) DB.committedAll

  unchanged : ∀ before → StoreStep.Result Validation.Fault → Proposal before
  unchanged before (StoreStep.done value) = committed before before value
  unchanged before reply@(StoreStep.needsInput _) = proposal before reply DB.abortedNone
  unchanged before StoreStep.needsRecovery = proposal before StoreStep.needsRecovery DB.abortedNone
  unchanged before reply@(StoreStep.cancelled _) = proposal before reply DB.abortedNone

  publishItem : Plan.Step → Bool → (before : Store.World) → Store.World → ItemResult → Proposal before
  publishItem statement final before candidate result with final
  ... | false = committed before (Store.saveAnswer candidate token (Plan.Step.id statement) (encodedItem result)) (encodedItem result)
  ... | true with countRows (A.Context.rows context)
    (Store.saveAnswer candidate token (Plan.Step.id statement) (encodedItem result))
  ... | nothing = unchanged before StoreStep.needsRecovery
  ... | just count = committed before (Store.saveAnswer
    (Store.saveAnswer candidate token (Plan.Step.id statement) (encodedItem result))
    token StoreStep.resultKey (encodedCounts count)) (encodedCounts count)

  fresh : Plan.Step → Bool → Preparation → Plan.CapturedSource → (before : Store.World) → Proposal before
  fresh statement final packet row before with
    intentForFinal final selected (A.semanticSource row) (preparedVector row packet) before
  ... | candidate , dialogue = unchanged before (StoreStep.needsInput (preparationFault packet))
  ... | candidate , skipped = publishItem statement final before candidate skipped
  ... | candidate , embedded = publishItem statement final before candidate embedded

  process : Plan.Step → Bool → Preparation → (before : Store.World) → Proposal before
  process statement final packet before with inspect before
  ... | terminal reply = unchanged before reply
  ... | ready with readySelection (A.Context.rows context) before
  ... | false = unchanged before (StoreStep.needsInput stale)
  ... | true with Store.lookupSaved before token (Plan.Step.id statement)
  ... | just saved with final
  ... | true = unchanged before StoreStep.needsRecovery
  ... | false with status saved
  ... | nothing = unchanged before StoreStep.needsRecovery
  ... | just _ = committed before before saved
  process statement final packet before | ready | true | nothing with findSource (Plan.Step.key statement)
  ... | nothing = unchanged before StoreStep.needsRecovery
  ... | just row = fresh statement final packet row before

  noPending : Bool
  noPending = null (Plan.Saved.steps (A.Context.plan context))

  finish : (before : Store.World) → Proposal before
  finish before with inspect before
  ... | terminal reply = unchanged before reply
  ... | ready with noPending
  ... | false = unchanged before StoreStep.needsRecovery
  ... | true with completeSelection selected before
  ... | false = unchanged before (StoreStep.needsInput stale)
  ... | true with countRows (A.Context.rows context) before
  ... | nothing = unchanged before StoreStep.needsRecovery
  ... | just count = committed before (Store.saveAnswer before token StoreStep.resultKey (encodedCounts count)) (encodedCounts count)

  record Declared : Set where
    constructor declared
    field statement : Plan.Step
          member : Contains statement (Plan.Saved.steps (A.Context.plan context))

  mark : ∀ {A : Set} (rows : List A) → List (Σ A (λ row → Contains row rows))
  mark [] = []
  mark (row ∷ rest) = (row , containsHere rest) ∷ map
    (λ { (item , member) → item , containsThere row rest member }) (mark rest)

  declarations : List Declared
  declarations = map (λ { (statement , member) → declared statement member })
    (mark (Plan.Saved.steps (A.Context.plan context)))

  data Effect : Set where
    inspectOriginal finishEmpty : Effect
    processItem : Declared → Bool → Effect

  Reply : Effect → Set
  Reply inspectOriginal = View
  Reply finishEmpty = StoreStep.Result Validation.Fault
  -- The packet is an observation of preparation for this declaration's
  -- complete captured input and original model. It is an effect reply, never
  -- an agent argument or a deterministic-provider assumption.
  Reply (processItem declaration final) = Preparation × StoreStep.Result Validation.Fault

  Atomic : Store.World → (effect : Effect) → Reply effect → Store.World → Set
  Atomic before inspectOriginal reply after = reply ≡ inspect before × after ≡ before
  Atomic before finishEmpty reply after = reply ≡ Proposal.returned (finish before) ×
    DB.Atomic before (Proposal.publicationWorld (finish before)) (StoreStep.receiptFor reply) after
  Atomic before (processItem declaration final) (packet , reply) after =
    reply ≡ Proposal.returned proposed × DB.Atomic before (Proposal.publicationWorld proposed) (StoreStep.receiptFor reply) after
    where proposed = process (Declared.statement declaration) final packet before

  module X = Recovery.Execution Store.World Effect Reply Atomic
  module E = X.E

  mutual
    run : List Declared → E.Script (StoreStep.Result Validation.Fault)
    run [] = E.ask finishEmpty E.done
    run (declaration ∷ []) = E.ask (processItem declaration true) (λ observed → E.done (proj₂ observed))
    run (declaration ∷ next ∷ rest) = E.ask (processItem declaration false)
      (λ observed → continue (next ∷ rest) (proj₂ observed))

    continue : List Declared → StoreStep.Result Validation.Fault → E.Script (StoreStep.Result Validation.Fault)
    continue remaining (StoreStep.done _) = run remaining
    continue remaining reply@(StoreStep.needsInput _) = E.done reply
    continue remaining StoreStep.needsRecovery = E.done StoreStep.needsRecovery
    continue remaining reply@(StoreStep.cancelled _) = E.done reply

  afterInspection : View → E.Script (StoreStep.Result Validation.Fault)
  afterInspection (terminal reply) = E.done reply
  afterInspection ready = run declarations

  script : ⊤ → E.Script (StoreStep.Result Validation.Fault)
  script _ = E.ask inspectOriginal afterInspection

  storedReceipt retainedReceipt : Wire.Value
  storedReceipt = Encoding.object (("status" , Wire.string (toList "embedded")) ∷ [])
  retainedReceipt = Encoding.object (("status" , Wire.string (toList "skipped")) ∷ [])

  -- Intended additions of business data and truthful acknowledgements. This
  -- relation permits any order and says nothing about SQL statements or crash
  -- points. A stored receipt requires an actual new vector; a skipped receipt
  -- requires preserving a vector already present at that publication.
  data Publications (original : Store.World) : Store.World → Set where
    originalPublications : Publications original original
    storedItem : ∀ before declaration row vector →
      Publications original before →
      findSource (Plan.Step.key (Declared.statement declaration)) ≡ just row →
      current (A.semanticSource row) before ≡ pendingVector → Backfill.usableVector vector ≡ true →
      Store.lookupSaved before token (Plan.Step.id (Declared.statement declaration)) ≡ nothing →
      Publications original (Store.saveAnswer
        (record before { beliefVectors = (Plan.CapturedSource.identity row , vector) ∷ Store.World.beliefVectors before })
        token (Plan.Step.id (Declared.statement declaration)) storedReceipt)
    retainedItem : ∀ before declaration row →
      Publications original before →
      findSource (Plan.Step.key (Declared.statement declaration)) ≡ just row →
      current (A.semanticSource row) before ≡ alreadyPresent →
      Store.lookupSaved before token (Plan.Step.id (Declared.statement declaration)) ≡ nothing →
      Publications original (Store.saveAnswer before token (Plan.Step.id (Declared.statement declaration)) retainedReceipt)
    completionAnswer : ∀ before count → Publications original before →
      completeSelection selected before ≡ true → countRows (A.Context.rows context) before ≡ just count →
      Store.lookupSaved before token StoreStep.resultKey ≡ nothing →
      Publications original (Store.saveAnswer before token StoreStep.resultKey (encodedCounts count))

  -- This fixed relation is the business goal. A new completion requires every
  -- selected source/vector AND the exact count of original saved item statuses.
  -- A previously completed request instead preserves the current whole world.
  data CompletionMeaning (original final : Store.World) : Set where
    stillPending : Store.lookupSaved original token StoreStep.resultKey ≡ nothing →
      Store.lookupSaved final token StoreStep.resultKey ≡ nothing → CompletionMeaning original final
    historical : ∀ value → Store.lookupSaved original token StoreStep.resultKey ≡ just value →
      final ≡ original → CompletionMeaning original final
    newlyComplete : Store.lookupSaved original token StoreStep.resultKey ≡ nothing →
      (count : Counts) → countRows (A.Context.rows context) final ≡ just count →
      Store.lookupSaved final token StoreStep.resultKey ≡ just (encodedCounts count) →
      completeSelection selected final ≡ true → CompletionMeaning original final

  Invariant : Store.World → Store.World → Set
  Invariant original final = Frame token keys selected original final ×
    Publications original final × CompletionMeaning original final

  ReplyMeaning : Store.World → StoreStep.Result Validation.Fault → Set
  ReplyMeaning final (StoreStep.done reply) = Store.lookupSaved final token StoreStep.resultKey ≡ just reply
  ReplyMeaning final _ = ⊤

  Goal : ⊤ → Store.World → Store.World → StoreStep.Result Validation.Fault → Set
  Goal _ original final reply = Invariant original final × ReplyMeaning final reply

  initialInvariant : ∀ original → Invariant original original
  initialInvariant original with Store.lookupSaved original token StoreStep.resultKey in result
  ... | nothing = initialFrame token keys selected original , originalPublications , stillPending result result
  ... | just value = initialFrame token keys selected original , originalPublications , historical value result refl

  justInjective : ∀ {A : Set} {first second : A} → just first ≡ just second → first ≡ second
  justInjective refl = refl

  newCompletionCoversWholeSelection : ∀ original final reply →
    Goal tt original final (StoreStep.done reply) →
    Store.lookupSaved original token StoreStep.resultKey ≡ nothing →
    All (λ source → completeSource source final ≡ true) selected ×
      Σ Counts (λ count → reply ≡ encodedCounts count × countRows (A.Context.rows context) final ≡ just count)
  newCompletionCoversWholeSelection original final reply
    ((frame , publications , stillPending _ absent) , saved) noOriginalResult with trans (sym absent) saved
  ... | ()
  newCompletionCoversWholeSelection original final reply
    ((frame , publications , historical value originalSaved same) , saved) noOriginalResult with trans (sym noOriginalResult) originalSaved
  ... | ()
  newCompletionCoversWholeSelection original final reply
    ((frame , publications , newlyComplete originalMissing count counted result complete) , saved) noOriginalResult =
    everySelectedSourceComplete selected final complete ,
    count , justInjective (trans (sym saved) result) , counted

  currentAfterAnswer : ∀ expected before operation key value →
    current expected (Store.saveAnswer before operation key value) ≡ current expected before
  currentAfterAnswer expected before operation key value with Store.lookupSaved before operation key
  ... | just _ = refl
  ... | nothing = refl

  completeAfterAnswer : ∀ sources before operation key value →
    completeSelection sources (Store.saveAnswer before operation key value) ≡ completeSelection sources before
  completeAfterAnswer [] before operation key value = refl
  completeAfterAnswer (expected ∷ rest) before operation key value
    rewrite currentAfterAnswer expected before operation key value |
      completeAfterAnswer rest before operation key value = refl

  countsAfterResult : ∀ rows before value →
    countRows rows (Store.saveAnswer before token StoreStep.resultKey value) ≡ countRows rows before
  countsAfterResult [] before value = refl
  countsAfterResult (row ∷ rest) before value
    rewrite countsAfterResult rest before value with countRows rest before
  ... | nothing = refl
  ... | just remaining with Plan.CapturedSource.alreadyEmbedded row
  ... | true = refl
  ... | false rewrite Store.otherSavedAnswerPreserved before token StoreStep.resultKey value token (rowKey row)
    (λ { (_ , same) → JournalEncoding.itemIsNotResult encoding row same }) = refl

  unchangedWorld : ∀ before reply → Proposal.publicationWorld (unchanged before reply) ≡ before
  unchangedWorld before (StoreStep.done _) = refl
  unchangedWorld before (StoreStep.needsInput _) = refl
  unchangedWorld before StoreStep.needsRecovery = refl
  unchangedWorld before (StoreStep.cancelled _) = refl

  originalWasPending : ∀ original before → CompletionMeaning original before →
    Store.lookupSaved before token StoreStep.resultKey ≡ nothing →
    Store.lookupSaved original token StoreStep.resultKey ≡ nothing
  originalWasPending original before (stillPending first current) absent = first
  originalWasPending original .original (historical value saved refl) absent with trans (sym absent) saved
  ... | ()
  originalWasPending original before (newlyComplete first count counted saved complete) absent with trans (sym absent) saved
  ... | ()

  resultOwns : memberText StoreStep.resultKey keys ≡ true
  resultOwns = memberTextHead StoreStep.resultKey (map Plan.Step.id (Plan.Saved.steps (A.Context.plan context)))

  declaredOwns : ∀ declaration → memberText (Plan.Step.id (Declared.statement declaration)) keys ≡ true
  declaredOwns declaration = memberTextTail (Plan.Step.id (Declared.statement declaration)) StoreStep.resultKey
    (map Plan.Step.id (Plan.Saved.steps (A.Context.plan context)))
    (mappedTextMember Plan.Step.id (Declared.member declaration))

  declaredNotResult : ∀ declaration → Plan.Step.id (Declared.statement declaration) ≡ StoreStep.resultKey → ⊥
  declaredNotResult declaration = JournalEncoding.declaredIsNotResult encoding (A.Context.plan context)
    (A.Context.validPlan context) (Declared.statement declaration) (Declared.member declaration)

  sourceFindMember : ∀ key row → findSource key ≡ just row → Contains row (A.Context.rows context)
  sourceFindMember nothing row ()
  sourceFindMember (just key) row foundSource with findSourceIn key (A.Context.rows context)
  ... | nothing with foundSource
  ... | ()
  sourceFindMember (just key) row foundSource | just (actual , member) with foundSource
  ... | refl = member

  readyHasNoResult : ∀ before → inspect before ≡ ready → Store.lookupSaved before token StoreStep.resultKey ≡ nothing
  readyHasNoResult before accepted with A.admit context before
  ... | just fault with accepted
  ... | ()
  readyHasNoResult before accepted | nothing with Store.lookupSaved before token StoreStep.resultKey
  ... | just saved with accepted
  ... | ()
  readyHasNoResult before accepted | nothing | nothing = refl

  existingDoneIsSaved : ∀ saved state reply → existingView saved state ≡ StoreStep.done reply → reply ≡ saved
  existingDoneIsSaved saved (Read.completed _ _) .saved refl = refl
  existingDoneIsSaved saved (Read.cancelled _ _ _) reply ()
  existingDoneIsSaved saved Read.unknownToken reply ()
  existingDoneIsSaved saved Read.reserved reply ()
  existingDoneIsSaved saved (Read.awaitingPlan _) reply ()
  existingDoneIsSaved saved (Read.awaitingCompletion _) reply ()
  existingDoneIsSaved saved (Read.pending _ _ _) reply ()
  existingDoneIsSaved saved (Read.needsRecovery _) reply ()
  existingDoneIsSaved saved (Read.inconsistent _ _) reply ()

  unfinishedCannotBeDone : ∀ state reply → unfinishedView state ≡ terminal (StoreStep.done reply) → ⊥
  unfinishedCannotBeDone Read.unknownToken reply ()
  unfinishedCannotBeDone Read.reserved reply ()
  unfinishedCannotBeDone (Read.awaitingPlan _) reply ()
  unfinishedCannotBeDone (Read.awaitingCompletion _) reply ()
  unfinishedCannotBeDone (Read.pending _ _ _) reply ()
  unfinishedCannotBeDone (Read.completed _ _) reply ()
  unfinishedCannotBeDone (Read.needsRecovery _) reply ()
  unfinishedCannotBeDone (Read.inconsistent _ _) reply ()
  unfinishedCannotBeDone (Read.cancelled _ _ _) reply ()

  inspectionDoneHasOriginalResult : ∀ before reply → inspect before ≡ terminal (StoreStep.done reply) →
    Store.lookupSaved before token StoreStep.resultKey ≡ just reply
  inspectionDoneHasOriginalResult before reply accepted with A.admit context before
  ... | just fault with accepted
  ... | ()
  inspectionDoneHasOriginalResult before reply accepted | nothing with Store.lookupSaved before token StoreStep.resultKey in saved
  ... | nothing = ⊥-elim (unfinishedCannotBeDone (Read.answer token before) reply accepted)
  ... | just value = cong just (sym (existingDoneIsSaved value (Read.answer token before) reply (unpack accepted)))
    where
    unpack : ∀ {first second} → terminal first ≡ terminal second → first ≡ second
    unpack refl = refl

  unchangedInvariant : ∀ original before reply → Invariant original before →
    Invariant original (Proposal.publicationWorld (unchanged before reply))
  unchangedInvariant original before reply prior = subst (Invariant original)
    (sym (unchangedWorld before reply)) prior

  itemMeaningOperations : ∀ expected before candidate result → ItemMeaning expected before candidate result →
    Store.World.operations candidate ≡ Store.World.operations before
  itemMeaningOperations expected before .before skipped (preservedVector _) = refl
  itemMeaningOperations expected before _ embedded (publishedVector _ _ _) = refl

  lookupSameOperations : ∀ candidate before key → Store.World.operations candidate ≡ Store.World.operations before →
    Store.lookupSaved candidate token key ≡ Store.lookupSaved before token key
  lookupSameOperations candidate before key same = cong
    (λ operations → Store.lookupReply token key (Store.OperationTables.savedReplies operations)) same

  itemPublications : ∀ original before declaration row candidate result →
    Publications original before →
    findSource (Plan.Step.key (Declared.statement declaration)) ≡ just row →
    Store.lookupSaved before token (Plan.Step.id (Declared.statement declaration)) ≡ nothing →
    ItemMeaning (A.semanticSource row) before candidate result →
    Publications original (Store.saveAnswer candidate token
      (Plan.Step.id (Declared.statement declaration)) (encodedItem result))
  itemPublications original before declaration row .before skipped prior foundSource absent (preservedVector seen) =
    retainedItem before declaration row prior foundSource seen absent
  itemPublications original before declaration row _ embedded prior foundSource absent (publishedVector vector seen usable) =
    storedItem before declaration row vector prior foundSource seen usable absent

  publishKeepsInvariant : ∀ declaration final row original before candidate result →
    Invariant original before → Frame token keys selected original candidate →
    findSource (Plan.Step.key (Declared.statement declaration)) ≡ just row →
    Store.lookupSaved before token (Plan.Step.id (Declared.statement declaration)) ≡ nothing →
    Store.lookupSaved before token StoreStep.resultKey ≡ nothing →
    ItemMeaning (A.semanticSource row) before candidate result →
    (final ≡ true → completeSelection selected candidate ≡ true) →
    Invariant original
      (Proposal.publicationWorld (publishItem (Declared.statement declaration) final before candidate result))
  publishKeepsInvariant declaration false row original before candidate result
    (priorFrame , priorPublications , priorMeaning) candidateFrame foundSource absent noResult meaning complete =
    savingAnswerKeepsFrame token keys selected original candidate key (encodedItem result) (declaredOwns declaration) candidateFrame ,
    itemPublications original before declaration row candidate result priorPublications foundSource absent meaning ,
    stillPending (originalWasPending original before priorMeaning noResult) preservedResult
    where
    key = Plan.Step.id (Declared.statement declaration)
    preservedResult = trans
      (Store.otherSavedAnswerPreserved candidate token key (encodedItem result) token StoreStep.resultKey
        (λ { (_ , same) → declaredNotResult declaration (sym same) }))
      (trans (lookupSameOperations candidate before StoreStep.resultKey
        (itemMeaningOperations (A.semanticSource row) before candidate result meaning)) noResult)
  publishKeepsInvariant declaration true row original before candidate result
    prior@(priorFrame , priorPublications , priorMeaning) candidateFrame foundSource absent noResult meaning complete
    with countRows (A.Context.rows context)
      (Store.saveAnswer candidate token (Plan.Step.id (Declared.statement declaration)) (encodedItem result)) in counted
  ... | nothing = prior
  ... | just count =
    savingAnswerKeepsFrame token keys selected original itemWorld StoreStep.resultKey (encodedCounts count) resultOwns
      (savingAnswerKeepsFrame token keys selected original candidate key (encodedItem result) (declaredOwns declaration) candidateFrame) ,
    completionAnswer itemWorld count
      (itemPublications original before declaration row candidate result priorPublications foundSource absent meaning)
      completeItem counted noItemResult ,
    newlyComplete (originalWasPending original before priorMeaning noResult) count
      (trans (countsAfterResult (A.Context.rows context) itemWorld (encodedCounts count)) counted)
      (savingMissingAnswerReadable itemWorld token StoreStep.resultKey (encodedCounts count) noItemResult)
      (trans (completeAfterAnswer selected itemWorld token StoreStep.resultKey (encodedCounts count)) completeItem)
    where
    key = Plan.Step.id (Declared.statement declaration)
    itemWorld = Store.saveAnswer candidate token key (encodedItem result)
    noItemResult = trans
      (Store.otherSavedAnswerPreserved candidate token key (encodedItem result) token StoreStep.resultKey
        (λ { (_ , same) → declaredNotResult declaration (sym same) }))
      (trans (lookupSameOperations candidate before StoreStep.resultKey
        (itemMeaningOperations (A.semanticSource row) before candidate result meaning)) noResult)
    completeItem = trans (completeAfterAnswer selected candidate token key (encodedItem result)) (complete refl)

  intentCompleteWhenFinal : ∀ final expected packet before candidate result → Successful result →
    intentForFinal final selected expected packet before ≡ (candidate , result) →
    final ≡ true → completeSelection selected candidate ≡ true
  intentCompleteWhenFinal false expected packet before candidate result successful intended ()
  intentCompleteWhenFinal true expected packet before candidate result successful intended refl =
    finalIntentComplete selected expected packet before candidate result successful intended

  freshKeepsInvariant : ∀ declaration final packet row original before →
    findSource (Plan.Step.key (Declared.statement declaration)) ≡ just row →
    Store.lookupSaved before token (Plan.Step.id (Declared.statement declaration)) ≡ nothing →
    Store.lookupSaved before token StoreStep.resultKey ≡ nothing → Invariant original before →
    Invariant original
      (Proposal.publicationWorld (fresh (Declared.statement declaration) final packet row before))
  freshKeepsInvariant declaration final packet row original before foundSource absent noResult prior
    with intentForFinal final selected (A.semanticSource row) (preparedVector row packet) before in intended |
      intentKeepsFrame final token keys selected original before (A.semanticSource row) (preparedVector row packet)
        (mapContains A.semanticSource (sourceFindMember (Plan.Step.key (Declared.statement declaration)) row foundSource)) (proj₁ prior)
  ... | candidate , dialogue | candidateFrame = unchangedInvariant original before
    (StoreStep.needsInput (preparationFault packet)) prior
  ... | candidate , skipped | candidateFrame = publishKeepsInvariant declaration final row original before candidate skipped
    prior candidateFrame foundSource absent noResult
    (intentSuccessMeaning final selected (A.semanticSource row) (preparedVector row packet) before candidate skipped tt intended)
    (intentCompleteWhenFinal final (A.semanticSource row) (preparedVector row packet) before candidate skipped tt intended)
  ... | candidate , embedded | candidateFrame = publishKeepsInvariant declaration final row original before candidate embedded
    prior candidateFrame foundSource absent noResult
    (intentSuccessMeaning final selected (A.semanticSource row) (preparedVector row packet) before candidate embedded tt intended)
    (intentCompleteWhenFinal final (A.semanticSource row) (preparedVector row packet) before candidate embedded tt intended)

  processKeepsInvariant : ∀ declaration final packet original before → Invariant original before →
    Invariant original
      (Proposal.publicationWorld (process (Declared.statement declaration) final packet before))
  processKeepsInvariant declaration final packet original before prior with inspect before in inspected
  ... | terminal reply = unchangedInvariant original before reply prior
  ... | ready with readySelection (A.Context.rows context) before
  ... | false = unchangedInvariant original before (StoreStep.needsInput stale) prior
  ... | true with Store.lookupSaved before token (Plan.Step.id (Declared.statement declaration)) in saved
  ... | just value with final
  ... | true = unchangedInvariant original before StoreStep.needsRecovery prior
  ... | false with status value
  ... | nothing = unchangedInvariant original before StoreStep.needsRecovery prior
  ... | just _ = prior
  processKeepsInvariant declaration final packet original before prior | ready | true | nothing
    with findSource (Plan.Step.key (Declared.statement declaration)) in foundSource
  ... | nothing = unchangedInvariant original before StoreStep.needsRecovery prior
  ... | just row = freshKeepsInvariant declaration final packet row original before foundSource saved
    (readyHasNoResult before inspected) prior

  finishKeepsInvariant : ∀ original before → Invariant original before →
    Invariant original (Proposal.publicationWorld (finish before))
  finishKeepsInvariant original before prior@(priorFrame , priorPublications , priorMeaning)
    with inspect before in inspected
  ... | terminal reply = unchangedInvariant original before reply prior
  ... | ready with noPending
  ... | false = unchangedInvariant original before StoreStep.needsRecovery prior
  ... | true with completeSelection selected before in complete
  ... | false = unchangedInvariant original before (StoreStep.needsInput stale) prior
  ... | true with countRows (A.Context.rows context) before in counted
  ... | nothing = unchangedInvariant original before StoreStep.needsRecovery prior
  ... | just count =
    savingAnswerKeepsFrame token keys selected original before StoreStep.resultKey (encodedCounts count) resultOwns priorFrame ,
    completionAnswer before count priorPublications complete counted (readyHasNoResult before inspected) ,
    newlyComplete (originalWasPending original before priorMeaning (readyHasNoResult before inspected)) count
      (trans (countsAfterResult (A.Context.rows context) before (encodedCounts count)) counted)
      (savingMissingAnswerReadable before token StoreStep.resultKey (encodedCounts count) (readyHasNoResult before inspected))
      (trans (completeAfterAnswer selected before token StoreStep.resultKey (encodedCounts count)) complete)

  atomicKeepsInvariant : ∀ original before effect reply after →
    Invariant original before → Atomic before effect reply after → Invariant original after
  atomicKeepsInvariant original before inspectOriginal reply after prior (same , refl) = prior
  atomicKeepsInvariant original before finishEmpty .(Proposal.returned (finish before)) after prior (refl , physical) =
    DB.invariantPreserved (Invariant original) physical prior (finishKeepsInvariant original before prior)
  atomicKeepsInvariant original before (processItem declaration final)
    (packet , .(Proposal.returned (process (Declared.statement declaration) final packet before))) after prior (refl , physical) =
    DB.invariantPreserved (Invariant original) physical prior
      (processKeepsInvariant declaration final packet original before prior)

  changesKeepInvariant : ∀ original {before events after} → Invariant original before →
    X.Changes before events after → Invariant original after
  changesKeepInvariant original prior (X.unchanged _) = prior
  changesKeepInvariant original prior (X.changed before effect reply middle physical rest) =
    changesKeepInvariant original (atomicKeepsInvariant original before effect reply middle prior physical) rest

  interruptionsKeepInvariant : ∀ initial interrupted → X.Interrupted (script tt) initial interrupted →
    Invariant initial interrupted
  interruptionsKeepInvariant initial interrupted (X.atPrefix events residual .interrupted prefix changes) =
    changesKeepInvariant initial (initialInvariant initial) changes
  interruptionsKeepInvariant initial interrupted
    (X.beforeReply events effect continuation current reply .interrupted prefix changes physical) =
    atomicKeepsInvariant initial current effect reply interrupted
      (changesKeepInvariant initial (initialInvariant initial) changes) physical

  publishFinalReturnsSaved : ∀ declaration row before candidate result value →
    Store.lookupSaved before token StoreStep.resultKey ≡ nothing →
    ItemMeaning (A.semanticSource row) before candidate result →
    Proposal.returned (publishItem (Declared.statement declaration) true before candidate result) ≡ StoreStep.done value →
    Store.lookupSaved (Proposal.publicationWorld (publishItem (Declared.statement declaration) true before candidate result))
      token StoreStep.resultKey ≡ just value
  publishFinalReturnsSaved declaration row before candidate result value noResult meaning accepted with
    countRows (A.Context.rows context) (Store.saveAnswer candidate token (Plan.Step.id (Declared.statement declaration)) (encodedItem result))
  ... | nothing with accepted
  ... | ()
  publishFinalReturnsSaved declaration row before candidate result value noResult meaning accepted | just count with accepted
  ... | refl = savingMissingAnswerReadable itemWorld token StoreStep.resultKey (encodedCounts count) noItemResult
    where
    key = Plan.Step.id (Declared.statement declaration)
    itemWorld = Store.saveAnswer candidate token key (encodedItem result)
    noItemResult = trans
      (Store.otherSavedAnswerPreserved candidate token key (encodedItem result) token StoreStep.resultKey
        (λ { (_ , same) → declaredNotResult declaration (sym same) }))
      (trans (lookupSameOperations candidate before StoreStep.resultKey
        (itemMeaningOperations (A.semanticSource row) before candidate result meaning)) noResult)

  freshFinalReturnsSaved : ∀ declaration packet row before value →
    Store.lookupSaved before token StoreStep.resultKey ≡ nothing →
    Proposal.returned (fresh (Declared.statement declaration) true packet row before) ≡ StoreStep.done value →
    Store.lookupSaved (Proposal.publicationWorld (fresh (Declared.statement declaration) true packet row before))
      token StoreStep.resultKey ≡ just value
  freshFinalReturnsSaved declaration packet row before value noResult accepted
    with intentForFinal true selected (A.semanticSource row) (preparedVector row packet) before in intended
  ... | candidate , dialogue with accepted
  ... | ()
  freshFinalReturnsSaved declaration packet row before value noResult accepted | candidate , skipped =
    publishFinalReturnsSaved declaration row before candidate skipped value noResult
      (intentSuccessMeaning true selected (A.semanticSource row) (preparedVector row packet) before candidate skipped tt intended) accepted
  freshFinalReturnsSaved declaration packet row before value noResult accepted | candidate , embedded =
    publishFinalReturnsSaved declaration row before candidate embedded value noResult
      (intentSuccessMeaning true selected (A.semanticSource row) (preparedVector row packet) before candidate embedded tt intended) accepted

  unchangedReturnsSaved : ∀ before returned value → ReplyMeaning before returned →
    Proposal.returned (unchanged before returned) ≡ StoreStep.done value →
    Store.lookupSaved (Proposal.publicationWorld (unchanged before returned)) token StoreStep.resultKey ≡ just value
  unchangedReturnsSaved before (StoreStep.done value) .value known refl = known
  unchangedReturnsSaved before (StoreStep.needsInput _) value known ()
  unchangedReturnsSaved before StoreStep.needsRecovery value known ()
  unchangedReturnsSaved before (StoreStep.cancelled _) value known ()

  terminalReplyMeaning : ∀ before returned → inspect before ≡ terminal returned → ReplyMeaning before returned
  terminalReplyMeaning before (StoreStep.done value) inspected = inspectionDoneHasOriginalResult before value inspected
  terminalReplyMeaning before (StoreStep.needsInput _) inspected = tt
  terminalReplyMeaning before StoreStep.needsRecovery inspected = tt
  terminalReplyMeaning before (StoreStep.cancelled _) inspected = tt

  processFinalReturnsSaved : ∀ declaration packet before value →
    Proposal.returned (process (Declared.statement declaration) true packet before) ≡ StoreStep.done value →
    Store.lookupSaved (Proposal.publicationWorld (process (Declared.statement declaration) true packet before))
      token StoreStep.resultKey ≡ just value
  processFinalReturnsSaved declaration packet before value accepted with inspect before in inspected
  ... | terminal returned = unchangedReturnsSaved before returned value (terminalReplyMeaning before returned inspected) accepted
  ... | ready with readySelection (A.Context.rows context) before
  ... | false with accepted
  ... | ()
  processFinalReturnsSaved declaration packet before value accepted | ready | true with
    Store.lookupSaved before token (Plan.Step.id (Declared.statement declaration))
  ... | just saved with accepted
  ... | ()
  processFinalReturnsSaved declaration packet before value accepted | ready | true | nothing with
    findSource (Plan.Step.key (Declared.statement declaration))
  ... | nothing with accepted
  ... | ()
  processFinalReturnsSaved declaration packet before value accepted | ready | true | nothing | just row =
    freshFinalReturnsSaved declaration packet row before value (readyHasNoResult before inspected) accepted

  finishReturnsSaved : ∀ before value → Proposal.returned (finish before) ≡ StoreStep.done value →
    Store.lookupSaved (Proposal.publicationWorld (finish before)) token StoreStep.resultKey ≡ just value
  finishReturnsSaved before value accepted with inspect before in inspected
  ... | terminal returned = unchangedReturnsSaved before returned value (terminalReplyMeaning before returned inspected) accepted
  ... | ready with noPending
  ... | false with accepted
  ... | ()
  finishReturnsSaved before value accepted | ready | true with completeSelection selected before
  ... | false with accepted
  ... | ()
  finishReturnsSaved before value accepted | ready | true | true with countRows (A.Context.rows context) before
  ... | nothing with accepted
  ... | ()
  finishReturnsSaved before value accepted | ready | true | true | just count with accepted
  ... | refl = savingMissingAnswerReadable before token StoreStep.resultKey (encodedCounts count) (readyHasNoResult before inspected)

  finishAtomicReplyMeaning : ∀ before reply after → Atomic before finishEmpty reply after → ReplyMeaning after reply
  finishAtomicReplyMeaning before (StoreStep.done value) .(Proposal.publicationWorld (finish before))
    (same , DB.committedAll) = finishReturnsSaved before value (sym same)
  finishAtomicReplyMeaning before (StoreStep.needsInput _) after physical = tt
  finishAtomicReplyMeaning before StoreStep.needsRecovery after physical = tt
  finishAtomicReplyMeaning before (StoreStep.cancelled _) after physical = tt

  finalAtomicReplyMeaning : ∀ declaration before packet reply after →
    Atomic before (processItem declaration true) (packet , reply) after → ReplyMeaning after reply
  finalAtomicReplyMeaning declaration before packet (StoreStep.done value)
    .(Proposal.publicationWorld (process (Declared.statement declaration) true packet before))
    (same , DB.committedAll) = processFinalReturnsSaved declaration packet before value (sym same)
  finalAtomicReplyMeaning declaration before packet (StoreStep.needsInput _) after physical = tt
  finalAtomicReplyMeaning declaration before packet StoreStep.needsRecovery after physical = tt
  finalAtomicReplyMeaning declaration before packet (StoreStep.cancelled _) after physical = tt

  mutual
    runReplyMeaning : ∀ rows before after reply {events} → E.Runs (run rows) events reply →
      X.Changes before events after → ReplyMeaning after reply
    runReplyMeaning [] before after reply
      (E.replied .finishEmpty _ .reply (E.returned .reply))
      (X.changed .before .finishEmpty .reply .after physical (X.unchanged .after)) =
      finishAtomicReplyMeaning before reply after physical
    runReplyMeaning (declaration ∷ []) before after reply
      (E.replied .(processItem declaration true) _ (packet , .reply) (E.returned .reply))
      (X.changed .before .(processItem declaration true) .(packet , reply) .after physical (X.unchanged .after)) =
      finalAtomicReplyMeaning declaration before packet reply after physical
    runReplyMeaning (declaration ∷ next ∷ rest) before after reply
      (E.replied .(processItem declaration false) _ (packet , itemReply) execution)
      (X.changed .before .(processItem declaration false) .(packet , itemReply) middle physical changes) =
      continueReplyMeaning (next ∷ rest) middle after itemReply reply execution changes

    continueReplyMeaning : ∀ rows before after itemReply reply {events} →
      E.Runs (continue rows itemReply) events reply → X.Changes before events after → ReplyMeaning after reply
    continueReplyMeaning rows before after (StoreStep.done _) reply execution changes =
      runReplyMeaning rows before after reply execution changes
    continueReplyMeaning rows before .before (StoreStep.needsInput fault) .(StoreStep.needsInput fault)
      (E.returned _) (X.unchanged _) = tt
    continueReplyMeaning rows before .before StoreStep.needsRecovery .StoreStep.needsRecovery
      (E.returned _) (X.unchanged _) = tt
    continueReplyMeaning rows before .before (StoreStep.cancelled cancellation) .(StoreStep.cancelled cancellation)
      (E.returned _) (X.unchanged _) = tt

  completedReplyMeaning : ∀ before after reply → X.Completed (script tt) before after reply → ReplyMeaning after reply
  completedReplyMeaning before after reply
    (X.completed ._ (E.replied .inspectOriginal _ view execution)
      (X.changed .before .inspectOriginal .view middle (refl , refl) changes))
    with inspect before in inspected
  ... | ready = runReplyMeaning declarations before after reply execution changes
  ... | terminal returned with execution | changes
  ... | E.returned .returned | X.unchanged .before = terminalReplyMeaning before returned inspected

  converges : ∀ input initial interrupted final reply →
    X.Interrupted (script input) initial interrupted → X.Completed (script input) interrupted final reply →
    Goal input initial final reply
  converges tt initial interrupted final reply interruptedRun completedRun =
    changesKeepInvariant initial (interruptionsKeepInvariant initial interrupted interruptedRun)
      (X.Completed.changes completedRun) , completedReplyMeaning interrupted final reply completedRun

  diagnosticPacket : Preparation
  diagnosticPacket = unavailable (toList "Provider preparation is unavailable; open a user dialog before any vector publication.")

  mutual
    runProgress : ∀ rows before → Σ Store.World (λ after → Σ (StoreStep.Result Validation.Fault)
      (λ reply → X.Completed (run rows) before after reply))
    runProgress [] before = after , reply , X.completed ((finishEmpty , reply) ∷ [])
      (E.replied finishEmpty E.done reply (E.returned reply))
      (X.changed before finishEmpty reply after (refl , Proposal.physical proposed) (X.unchanged after))
      where
      proposed = finish before
      after = Proposal.publicationWorld proposed
      reply = Proposal.returned proposed
    runProgress (declaration ∷ []) before = after , reply ,
      X.completed ((processItem declaration true , diagnosticPacket , reply) ∷ [])
        (E.replied (processItem declaration true) (λ observed → E.done (proj₂ observed))
          (diagnosticPacket , reply) (E.returned reply))
        (X.changed before (processItem declaration true) (diagnosticPacket , reply) after
          (refl , Proposal.physical proposed) (X.unchanged after))
      where
      proposed = process (Declared.statement declaration) true diagnosticPacket before
      after = Proposal.publicationWorld proposed
      reply = Proposal.returned proposed
    runProgress (declaration ∷ next ∷ rest) before
      with continueProgress (next ∷ rest)
        (Proposal.returned (process (Declared.statement declaration) false diagnosticPacket before))
        (Proposal.publicationWorld (process (Declared.statement declaration) false diagnosticPacket before))
    ... | after , reply , X.completed events execution changes = after , reply ,
      X.completed ((processItem declaration false , diagnosticPacket , itemReply) ∷ events)
        (E.replied (processItem declaration false) (λ observed → continue (next ∷ rest) (proj₂ observed))
          (diagnosticPacket , itemReply) execution)
        (X.changed before (processItem declaration false) (diagnosticPacket , itemReply) middle
          (refl , Proposal.physical proposed) changes)
      where
      proposed = process (Declared.statement declaration) false diagnosticPacket before
      middle = Proposal.publicationWorld proposed
      itemReply = Proposal.returned proposed

    continueProgress : ∀ rows itemReply before → Σ Store.World (λ after → Σ (StoreStep.Result Validation.Fault)
      (λ reply → X.Completed (continue rows itemReply) before after reply))
    continueProgress rows (StoreStep.done _) before = runProgress rows before
    continueProgress rows reply@(StoreStep.needsInput _) before =
      before , reply , X.completed [] (E.returned reply) (X.unchanged before)
    continueProgress rows StoreStep.needsRecovery before =
      before , StoreStep.needsRecovery , X.completed [] (E.returned StoreStep.needsRecovery) (X.unchanged before)
    continueProgress rows reply@(StoreStep.cancelled _) before =
      before , reply , X.completed [] (E.returned reply) (X.unchanged before)

  progress : ∀ input initial → Σ Store.World (λ final → Σ (StoreStep.Result Validation.Fault)
    (λ reply → X.Completed (script input) initial final reply))
  progress tt initial with inspect initial in inspected
  ... | terminal reply = initial , reply , X.completed ((inspectOriginal , terminal reply) ∷ [])
    (E.replied inspectOriginal afterInspection (terminal reply) (E.returned reply))
    (X.changed initial inspectOriginal (terminal reply) initial (sym inspected , refl) (X.unchanged initial))
  ... | ready with runProgress declarations initial
  ... | final , reply , X.completed events execution changes = final , reply ,
    X.completed ((inspectOriginal , ready) ∷ events)
      (E.replied inspectOriginal afterInspection ready execution)
      (X.changed initial inspectOriginal ready initial (sym inspected , refl) changes)

  operation : Recovery.RecoverableFor Store.World ⊤ (StoreStep.Result Validation.Fault) Goal
  operation = record
    { Effect = Effect; Reply = Reply; script = script; Atomic = Atomic
    ; converges = converges; progress = progress }

  admittedContextSurvivesBody : ∀ original final → Invariant original final →
    A.original token (StoreStep.registration original) ≡ inj₂ context →
    A.original token (StoreStep.registration final) ≡ inj₂ context
  admittedContextSurvivesBody original final invariant admitted = trans
    (cong (A.original token) (frameKeepsRegistration token keys selected original final (proj₁ invariant))) admitted
