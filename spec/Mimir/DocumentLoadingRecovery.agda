{-# OPTIONS --safe #-}
-- A saved original preparation fixes the file, PostgreSQL identities and old
-- document view. Provider work cannot replace that capture on a later retry.
module Mimir.DocumentLoadingRecovery where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Empty using (⊥)
open import Data.Float.Base using (Float)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_; map; length; zip; filterᵇ; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String using (String; toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.ApplicationStore as Store
import Mimir.DocumentStore as Documents
import Mimir.DocumentReplacementRecovery as Replacement
import Mimir.DocumentQuery as Query
import Mimir.Markdown as Markdown
import Mimir.PublicEncoding as Encoding
import Mimir.StandardLibrary as Library
import Mimir.PublicInput as Input
import Mimir.RecordDecoding as Record
import Mimir.StructuredValue as Wire
import Mimir.JsonObjects as Objects
import Mimir.Validation as Validation
import Mimir.RetrievalRanking as Ranking
import Mimir.Binary64 as Binary
import Mimir.PublicRequest as PublicRequest
import Mimir.ToolCatalog as Tools
import Mimir.IndependentBeliefRecovery as Belief
import Mimir.GroundingRecovery as Grounding
import Mimir.PosteriorComputation as P
import Mimir.RecoverableStoreStep as Step
import Mimir.RecoverableStoreSequence as Sequence
import Mimir.RegisteredStoreAdmission as Admission
import Mimir.Text as Text
import Mimir.SemanticKey as Key
import Mimir.LearningKeys as Keys
import Mimir.DatabaseTransaction as DB
import Mimir.ConfigurationValues as Config
import Mimir.ProjectDeletion as Project
import Mimir.Effects as Effects
import Mimir.Recovery as Recovery
import Mimir.OperationControls as Controls
import Data.List.Properties as Lists
open import Mimir.RecordDecoding using (_>>=_)

record Draft : Set where
  constructor draft
  field requestedPath path source : Text; project : Maybe Text

-- This fixed IO protocol names the actual path passed to each filesystem
-- operation. Its replies are external observations, not request fields.
module FileObservation where
  data Effect : Set where
    canonicalize readUTF8 : Text → Effect
  Reply : Effect → Set
  Reply _ = Validation.Fault ⊎ Text
  module E = Effects.Protocol Effect Reply
  afterPath : Text → Maybe Text → Validation.Fault ⊎ Text → E.Script (Validation.Fault ⊎ Draft)
  afterPath requested project (inj₁ fault) = E.done (inj₁ fault)
  afterPath requested project (inj₂ canonical) = E.ask (readUTF8 canonical) λ where
    (inj₁ fault) → E.done (inj₁ fault)
    (inj₂ source) → E.done (inj₂ (draft requested canonical source project))
  script : Text → Maybe Text → E.Script (Validation.Fault ⊎ Draft)
  script requested project = E.ask (canonicalize requested) (afterPath requested project)

-- These are temporary section links, not persistent identities. All saved
-- chunk and parent identities below are replaced by actual PostgreSQL replies.
outline : Draft → List Documents.Chunk
outline input = Parser.parse (Draft.source input)
  where module Parser = Markdown.Parse (Draft.path input) (Draft.project input) (λ ordinal → ordinal)

record Allocation : Set where
  constructor allocated
  field owner : ℕ; reservedAt : ℤ; declaredDimensions : Maybe ℕ; chunkIDs : List ℕ

record Prepared : Set where
  constructor prepared
  field owner : ℕ; reservedAt : ℤ; declaredDimensions : Maybe ℕ
        project : Maybe Text; path source : Text
        chunks previous : List Documents.Chunk

shapeFault : Validation.Fault
shapeFault = Validation.fault [] Validation.malformedInput
  "The original complete document preparation could not retain its allocated chunk identities and parent links. Read its saved preparation and outcome; no replacement was published."

lookupIdentity : ℕ → List (ℕ × ℕ) → Maybe ℕ
lookupIdentity identity [] = nothing
lookupIdentity identity ((key , assigned) ∷ rest) with identity ≟ key
... | yes _ = just assigned
... | no _ = lookupIdentity identity rest

remapParent : List (ℕ × ℕ) → Maybe ℕ → Validation.Fault ⊎ Maybe ℕ
remapParent mapping nothing = inj₂ nothing
remapParent mapping (just temporary) with lookupIdentity temporary mapping
... | nothing = inj₁ shapeFault
... | just assigned = inj₂ (just assigned)

remap : List (ℕ × ℕ) → List Documents.Chunk → Validation.Fault ⊎ List Documents.Chunk
remap mapping [] = inj₂ []
remap mapping (chunk ∷ rest) with lookupIdentity (Documents.Chunk.identity chunk) mapping
... | nothing = inj₁ shapeFault
... | just assigned = remapParent mapping (Documents.Chunk.parent chunk) >>= λ parent →
  remap mapping rest >>= λ later → inj₂ (record chunk { identity = assigned; parent = parent } ∷ later)

allocatedChunks : Draft → Allocation → Validation.Fault ⊎ List Documents.Chunk
allocatedChunks input metadata with length (outline input) ≟ length (Allocation.chunkIDs metadata)
... | no _ = inj₁ shapeFault
... | yes _ = remap (zip (map Documents.Chunk.identity (outline input)) (Allocation.chunkIDs metadata)) (outline input)

documentRows : Text → Store.World → List Documents.Chunk
documentRows path before = Ranking.sort
  (λ first second → does (Documents.Chunk.identity first Data.Nat.≤? Documents.Chunk.identity second))
  (filterᵇ (λ chunk → does (Documents.Chunk.document chunk ≟Text path)) (Store.World.chunks before))

capture : Draft → Allocation → Store.World → Validation.Fault ⊎ Prepared
capture input metadata snapshot = allocatedChunks input metadata >>= λ chunks → inj₂
  (prepared (Allocation.owner metadata) (Allocation.reservedAt metadata) (Allocation.declaredDimensions metadata)
    (Draft.project input) (Draft.path input) (Draft.source input) chunks (documentRows (Draft.path input) snapshot))

module Codec (library : Library.Contract) (format : Encoding.Formatting)
  (utcTimestamp : Text → Validation.Fault ⊎ ℤ) where
  module Encode = Encoding.Encode format
  module Scalar = Input.Numbers library

  optionalField : ∀ {A : Set} → String → (A → Wire.Value) → Maybe A → List (String × Wire.Value)
  optionalField name encode nothing = []
  optionalField name encode (just value) = (name , encode value) ∷ []

  chunk : Documents.Chunk → Wire.Value
  chunk value = Encoding.object
    (("id" , Encode.uuid (Documents.Chunk.identity value)) ∷
     ("document_path" , Wire.string (Documents.Chunk.document value)) ∷
     ("section_path" , Wire.array (map Wire.string (Documents.Chunk.section value))) ∷
     ("content" , Wire.string (Documents.Chunk.content value)) ∷
     (optionalField "parent_id" Encode.uuid (Documents.Chunk.parent value)
      Data.List.++ optionalField "project" Wire.string (Documents.Chunk.project value)))

  encode : Prepared → Wire.Value
  encode value = Encoding.object
    (("owner_token" , Encode.uuid (Prepared.owner value)) ∷
     ("reserved_at" , Encode.timestamp (Prepared.reservedAt value)) ∷
     ("declared_dimensions" , Encoding.optional Wire.unsigned (Prepared.declaredDimensions value)) ∷
     ("project" , Encoding.optional Wire.string (Prepared.project value)) ∷
     ("path" , Wire.string (Prepared.path value)) ∷
     ("source" , Wire.string (Prepared.source value)) ∷
     ("chunks" , Wire.array (map chunk (Prepared.chunks value))) ∷
     ("previous" , Wire.array (map chunk (Prepared.previous value))) ∷ [])

  readChunk : Wire.Value → Validation.Fault ⊎ Documents.Chunk
  readChunk = Record.readRecord Objects.forbid Objects.rejectKnownRepeated
    (map toList ("id" ∷ "document_path" ∷ "section_path" ∷ "content" ∷ "parent_id" ∷ "project" ∷ [])) λ fields →
      Input.required "id" Scalar.uuid fields >>= λ identity →
      Input.required "document_path" Wire.asString fields >>= λ path →
      Input.required "section_path" (Record.readArray Wire.asString) fields >>= λ section →
      Input.required "content" Wire.asString fields >>= λ content →
      Input.optional "parent_id" Scalar.uuid fields >>= λ parent →
      Input.optional "project" Wire.asString fields >>= λ project →
      inj₂ (Documents.mkChunk identity path section content parent project)

  decode : Wire.Value → Validation.Fault ⊎ Prepared
  decode = Record.readRecord Objects.forbid Objects.rejectKnownRepeated
    (map toList ("owner_token" ∷ "reserved_at" ∷ "declared_dimensions" ∷ "project" ∷ "path" ∷ "source" ∷ "chunks" ∷ "previous" ∷ [])) λ fields →
      Input.required "owner_token" Scalar.uuid fields >>= λ owner →
      Input.required "reserved_at" (λ raw → Wire.asString raw >>= utcTimestamp) fields >>= λ reserved →
      -- The existing installed target's usize representation, not a quota.
      Input.optional "declared_dimensions" (Input.unsigned (Binary.powerMinusOne 64)) fields >>= λ dimension →
      Input.optional "project" Wire.asString fields >>= λ project →
      Input.required "path" Wire.asString fields >>= λ path →
      Input.required "source" Wire.asString fields >>= λ source →
      Input.required "chunks" (Record.readArray readChunk) fields >>= λ chunks →
      Input.required "previous" (Record.readArray readChunk) fields >>= λ previous →
      inj₂ (prepared owner reserved dimension project path source chunks previous)

  -- An actual successful standard serialization/deserialization receipt for
  -- these concrete fields. No universal UUID/date formatter law is assumed.
  record Candidate (value : Prepared) : Set where
    field decoded : decode (encode value) ≡ inj₂ value

record Request : Set where
  constructor request
  field path : Text; project : Maybe Text

preparationKey publicationKey : ℕ → Text
preparationKey _ = toList "[\"store.prepare_document\",null]"
publicationKey _ = toList "[\"store.replace_document\",null]"
preparationDistinct : ∀ token → preparationKey token ≡ Step.resultKey → ⊥
preparationDistinct token ()
publicationDistinct : ∀ token → publicationKey token ≡ Step.resultKey → ⊥
publicationDistinct token ()
phasesDifferent : ∀ token → preparationKey token ≡ publicationKey token → ⊥
phasesDifferent token ()

module Registered (library : Library.Contract) (format : Encoding.Formatting)
  (utcTimestamp : Text → Validation.Fault ⊎ ℤ)
  (databaseSum : List Float → Float) (calculator : P.Calculator)
  (serverTime : ℕ → Store.World → ℤ) where
  module C = Codec library format utcTimestamp
  module D = PublicRequest.Decode library
  module G = Grounding.Business databaseSum calculator
  module B dimension = Replacement.Business dimension databaseSum calculator

  descriptor = Admission.pairDescriptor (toList "load_document")
    (toList "store.prepare_document") (preparationKey 0)
    (toList "store.replace_document") (publicationKey 0)

  mismatch : Validation.Fault
  mismatch = Validation.fault (Validation.key "operation_token" ∷ []) Validation.wrongIdentity
    "Read this token's original document path, project, embedding settings and outcome. Ask the user before cancelling unfinished work and reserving corrected work; do not replace the saved file preparation."

  nonblank : Text → Validation.Fault ⊎ Text
  nonblank text with Text.nonblank? text
  ... | yes _ = inj₂ text
  ... | no _ = inj₁ (Validation.fault [] Validation.emptyText
    "Supply the intended nonblank document path and, when supplied, project. Open a user dialog if either is unknown; the existing index was not changed.")
  optionalProject : Maybe Text → Validation.Fault ⊎ Maybe Text
  optionalProject nothing = inj₂ nothing
  optionalProject (just project) = nonblank project >>= λ checked → inj₂ (just checked)

  arguments : Wire.Value → Validation.Fault ⊎ Request
  arguments raw with D.readBoundTool Tools.loadDocument raw
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ (PublicRequest.loadDocument path project) = nonblank path >>= λ checkedPath →
    optionalProject project >>= λ checkedProject → inj₂ (request checkedPath checkedProject)
  ... | inj₂ _ = inj₁ mismatch

  original : ℕ → Step.Registration → Validation.Fault ⊎ Request
  original token registration with Admission.resolvePair descriptor token registration
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ (_ , binding) with Belief.ProviderSettings.admitted (Store.BindingRow.settings binding)
  ... | false = inj₁ mismatch
  ... | true = arguments (Store.BindingRow.arguments binding)

  -- These are backend replies. The public script supplies no allocation,
  -- file content or snapshot in its invocation input. Successful serialization
  -- is tied to the concrete capture of this actual statement observation.
  data PreparationObservation : Set where
    unavailable : Validation.Fault → PreparationObservation
    observed : (input : Draft) (metadata : Allocation) (snapshot : Store.World) (value : Prepared) →
      capture input metadata snapshot ≡ inj₂ value → C.Candidate value → PreparationObservation

  Internal = ℕ × PreparationObservation
  admitOriginal : ℕ → Step.Registration → Maybe G.Diagnostic
  admitOriginal token registration with original token registration
  ... | inj₁ fault = just (G.requestFault fault)
  ... | inj₂ _ = nothing
  admit : Internal → Step.Registration → Maybe G.Diagnostic
  admit (token , metadata) = admitOriginal token

  sameProject : Maybe Text → Maybe Text → Bool
  sameProject nothing nothing = true
  sameProject (just first) (just second) = does (first ≟Text second)
  sameProject _ _ = false
  sameRequest : Request → Draft → Bool
  sameRequest actual input = does (Request.path actual ≟Text Draft.requestedPath input) ∧
    sameProject (Request.project actual) (Draft.project input)

  addOwner : ℕ → Allocation → Maybe Text → Store.World → Store.World
  addOwner token metadata project before = record before
    { embeddingOwners = Store.embeddingOwnerRow (Allocation.owner metadata) project (Allocation.reservedAt metadata) (just token)
      ∷ Store.World.embeddingOwners before }

  prepare : ℕ → PreparationObservation → Request → Store.World → G.Outcome
  prepare token (unavailable fault) actual before = inj₁ (G.requestFault fault)
  prepare token (observed input metadata snapshot value captured serialized) actual before with sameRequest actual input
  ... | false = inj₁ (G.requestFault mismatch)
  ... | true with capture input metadata before
  ... | inj₁ fault = inj₁ (G.requestFault fault)
  ... | inj₂ preparedValue = inj₂ (addOwner token metadata (Request.project actual) before , C.encode preparedValue)

  decidePreparation : Internal → Store.World → G.Outcome
  decidePreparation (token , metadata) before with original token (Step.registration before)
  ... | inj₁ fault = inj₁ (G.requestFault fault)
  ... | inj₂ actual = prepare token metadata actual before

  preparationJournal : ∀ input before after reply → decidePreparation input before ≡ inj₂ (after , reply) →
    Store.World.operations after ≡ Store.World.operations before
  preparationJournal (token , metadata) before after reply accepted with original token (Step.registration before)
  ... | inj₁ fault with accepted
  ... | ()
  preparationJournal (token , unavailable fault) before after reply () | inj₂ actual
  preparationJournal (token , observed input metadata snapshot value captured serialized) before after reply accepted | inj₂ actual
    with sameRequest actual input
  ... | false with accepted
  ... | ()
  preparationJournal (token , observed input metadata snapshot value captured serialized) before after reply accepted | inj₂ actual | true
    with capture input metadata before
  ... | inj₁ fault with accepted
  ... | ()
  preparationJournal (token , observed input metadata snapshot value captured serialized) before ._ ._ refl | inj₂ actual | true | inj₂ preparedValue = refl

  module Prefix = Sequence.SavedPrefix Internal G.Diagnostic proj₁
    (λ input → preparationKey (proj₁ input)) (λ input → publicationKey (proj₁ input))
    (λ input → preparationDistinct (proj₁ input)) (λ input → phasesDifferent (proj₁ input))
    decidePreparation preparationJournal admit

  chunkKey : Documents.Chunk → Key.Key
  chunkKey chunk = Key.fields
    (Key.natural (Documents.Chunk.identity chunk) ∷ Key.text (Documents.Chunk.document chunk) ∷
     Keys.many Key.text (Documents.Chunk.section chunk) ∷ Key.text (Documents.Chunk.content chunk) ∷
     Keys.optional Key.natural (Documents.Chunk.parent chunk) ∷ Keys.optional Key.text (Documents.Chunk.project chunk) ∷ [])
  sameChunks : List Documents.Chunk → List Documents.Chunk → Bool
  sameChunks first second = does (Key.equal (Keys.many chunkKey first) (Keys.many chunkKey second))

  owns : ℕ → Prepared → Store.EmbeddingOwnerRow → Bool
  owns token value row = does (Prepared.owner value ≟ Store.EmbeddingOwnerRow.token row) ∧
    sameProject (Prepared.project value) (Store.EmbeddingOwnerRow.project row) ∧
    operationMatches (Store.EmbeddingOwnerRow.operationToken row)
    where
    operationMatches : Maybe ℕ → Bool
    operationMatches nothing = false
    operationMatches (just originalToken) = does (token ≟ originalToken)
  hasOwner : ℕ → Prepared → List Store.EmbeddingOwnerRow → Bool
  hasOwner token value [] = false
  hasOwner token value (row ∷ rest) with owns token value row
  ... | true = true
  ... | false = hasOwner token value rest

  consumeOwner : ℕ → Prepared → Store.World → Store.World
  consumeOwner token value before = record before
    { embeddingOwners = filterᵇ (λ row → Data.Bool.not (owns token value row)) (Store.World.embeddingOwners before) }

  storedPreparation : ℕ → Store.World → Validation.Fault ⊎ Prepared
  storedPreparation token before with Store.lookupSaved before token (preparationKey token)
  ... | nothing = inj₁ mismatch
  ... | just raw = C.decode raw

  stale : Validation.Fault
  stale = Validation.fault (Validation.key "operation_token" ∷ []) Validation.missingReference
    "Document preparation was revoked or its original indexed rows changed. Read the original token's preparation and outcome, then open a user dialog before retrying or explicitly cancelling. The previous index was not replaced."
  embeddingFault : Validation.Fault
  embeddingFault = Validation.fault (Validation.key "embeddings" ∷ []) Validation.malformedInput
    "The original document requires one complete finite nonzero vector per saved chunk, all in the same model space and respecting the actual column dimension when declared. Repair that backend and retry the same token; do not drop chunks, truncate inputs or invent vectors."

  dimension : List Store.Vector → ℕ
  dimension [] = 0
  dimension (vector ∷ _) = length vector
  batchValid : Prepared → List Store.Vector → Bool
  batchValid value vectors = does (length (Prepared.chunks value) ≟ length vectors) ∧ allVectors vectors ∧ allChunks (Prepared.chunks value)
    where
    columnMatches : Store.Vector → Bool
    columnMatches vector with Prepared.declaredDimensions value
    ... | nothing = true
    ... | just declared = does (length vector ≟ declared)
    allVectors : List Store.Vector → Bool
    allVectors [] = true
    allVectors (vector ∷ later) = Query.usableVector vector ∧ does (length vector ≟ dimension vectors) ∧
      columnMatches vector ∧ allVectors later
    allChunks : List Documents.Chunk → Bool
    allChunks [] = true
    allChunks (chunk ∷ later) = does (Documents.Chunk.document chunk ≟Text Prepared.path value) ∧ allChunks later

  record PublicationObservation : Set where
    constructor publication
    field vectors : Validation.Fault ⊎ List Store.Vector; publicationTime : ℤ

  backendFault : Text → Validation.Fault
  backendFault reason = Validation.fault (Validation.key "embeddings" ∷ []) Validation.missingEvidence
    (Data.String.fromList (toList "Embedding the saved original document could not finish: " Data.List.++ reason))

  calculate : ℕ → Prepared → PublicationObservation → Store.World → G.Outcome
  calculate token value received before with PublicationObservation.vectors received
  ... | inj₁ fault = inj₁ (G.requestFault fault)
  ... | inj₂ vectors with batchValid value vectors
  ... | false = inj₁ (G.requestFault embeddingFault)
  ... | true with proj₁ (B.checked (dimension vectors) (PublicationObservation.publicationTime received)
    (Prepared.path value) (Prepared.chunks value) vectors before)
  ... | inj₁ diagnostic = inj₁ diagnostic
  ... | inj₂ (changed , reply) = inj₂ (consumeOwner token value changed , reply)

  decidePublication : ℕ × PublicationObservation → Store.World → G.Outcome
  decidePublication (token , received) before with original token (Step.registration before)
  ... | inj₁ fault = inj₁ (G.requestFault fault)
  ... | inj₂ actual with storedPreparation token before
  ... | inj₁ fault = inj₁ (G.requestFault fault)
  ... | inj₂ value with sameProject (Request.project actual) (Prepared.project value) ∧
    hasOwner token value (Store.World.embeddingOwners before) ∧
    sameChunks (documentRows (Prepared.path value) before) (Prepared.previous value)
  ... | false = inj₁ (G.requestFault stale)
  ... | true = calculate token value received before

  calculateJournal : ∀ token value received before after reply → calculate token value received before ≡ inj₂ (after , reply) →
    Store.World.operations after ≡ Store.World.operations before
  calculateJournal token value received before after reply accepted with PublicationObservation.vectors received
  ... | inj₁ reason with accepted
  ... | ()
  calculateJournal token value received before after reply accepted | inj₂ vectors with batchValid value vectors
  ... | false with accepted
  ... | ()
  calculateJournal token value received before after reply accepted | inj₂ vectors | true
    with proj₁ (B.checked (dimension vectors) (PublicationObservation.publicationTime received)
      (Prepared.path value) (Prepared.chunks value) vectors before) in calculated
  ... | inj₁ diagnostic with accepted
  ... | ()
  calculateJournal token value received before ._ ._ refl | inj₂ vectors | true | inj₂ (changed , answer) =
    B.journalUnchanged (dimension vectors) (PublicationObservation.publicationTime received)
      (Prepared.path value) (Prepared.chunks value) vectors before changed answer calculated

  publicationJournal : ∀ input before after reply → decidePublication input before ≡ inj₂ (after , reply) →
    Store.World.operations after ≡ Store.World.operations before
  publicationJournal (token , received) before after reply accepted with original token (Step.registration before)
  ... | inj₁ fault with accepted
  ... | ()
  publicationJournal (token , received) before after reply accepted | inj₂ actual with storedPreparation token before
  ... | inj₁ fault with accepted
  ... | ()
  publicationJournal (token , received) before after reply accepted | inj₂ actual | inj₂ value
    with sameProject (Request.project actual) (Prepared.project value) ∧
      hasOwner token value (Store.World.embeddingOwners before) ∧
      sameChunks (documentRows (Prepared.path value) before) (Prepared.previous value)
  ... | false with accepted
  ... | ()
  publicationJournal (token , received) before after reply accepted | inj₂ actual | inj₂ value | true =
    calculateJournal token value received before after reply accepted

  admitPublication : ℕ × PublicationObservation → Step.Registration → Maybe G.Diagnostic
  admitPublication (token , received) = admitOriginal token

  module Final = Step.Admitted (ℕ × PublicationObservation) G.Diagnostic proj₁
    (λ input → publicationKey (proj₁ input)) (λ input → publicationDistinct (proj₁ input))
    decidePublication publicationJournal admitPublication

  -- The final goal uses the reviewed independent replacement/numerical goal,
  -- then consumes exactly this operation's owned preparation. No SQL steps or
  -- freely selected "expected world" occur in the business condition.
  ValidPublicationGoal : ℕ → Prepared → ℤ → List Store.Vector → Store.World → G.Outcome → Set
  ValidPublicationGoal token value received vectors before (inj₁ diagnostic) =
    B.Goal (dimension vectors) received (Prepared.path value) (Prepared.chunks value) vectors before (inj₁ diagnostic)
  ValidPublicationGoal token value received vectors before (inj₂ (after , reply)) = Σ Store.World (λ replaced →
    B.Goal (dimension vectors) received (Prepared.path value) (Prepared.chunks value) vectors before (inj₂ (replaced , reply)) ×
    after ≡ consumeOwner token value replaced)

  PreparedGoal : ℕ → Prepared → PublicationObservation → Store.World → G.Outcome → Set
  PreparedGoal token value received before outcome with PublicationObservation.vectors received
  ... | inj₁ fault = outcome ≡ inj₁ (G.requestFault fault)
  ... | inj₂ vectors with batchValid value vectors
  ... | false = outcome ≡ inj₁ (G.requestFault embeddingFault)
  ... | true = ValidPublicationGoal token value (PublicationObservation.publicationTime received) vectors before outcome

  calculateMeaning : ∀ token value received before → PreparedGoal token value received before (calculate token value received before)
  calculateMeaning token value received before with PublicationObservation.vectors received
  ... | inj₁ reason = refl
  ... | inj₂ vectors with batchValid value vectors
  ... | false = refl
  ... | true with B.checked (dimension vectors) (PublicationObservation.publicationTime received)
    (Prepared.path value) (Prepared.chunks value) vectors before
  ... | inj₁ diagnostic , correct = correct
  ... | inj₂ (changed , reply) , correct = changed , correct , refl

  first : PreparationObservation → ℕ → Store.World → Store.World × Step.Result G.Diagnostic
  first metadata token = Prefix.execute (token , metadata)
  firstStable : ∀ metadata token before → first metadata token (proj₁ (first metadata token before)) ≡ first metadata token before
  firstStable metadata token before = Prefix.stable (token , metadata) before
  firstPhysical : ∀ metadata token before → DB.Atomic before (proj₁ (first metadata token before))
    (Step.receiptFor (proj₂ (first metadata token before))) (proj₁ (first metadata token before))
  firstPhysical metadata token before = Prefix.expectedPhysical (token , metadata) before

  publishedPrefix : ∀ token received before changed reply → decidePublication (token , received) before ≡ inj₂ (changed , reply) →
    Store.lookupSaved (Final.Kernel.publication (token , received) changed reply) token (preparationKey token) ≡
    Store.lookupSaved before token (preparationKey token)
  publishedPrefix token received before changed reply accepted = trans
    (Store.otherSavedAnswerPreserved (Final.Kernel.firstPublication (token , received) changed reply) token Step.resultKey reply
      token (preparationKey token) (λ same → preparationDistinct token (proj₂ same)))
    (trans (Store.otherSavedAnswerPreserved changed token (publicationKey token) reply token (preparationKey token)
      (λ same → phasesDifferent token (proj₂ same)))
      (Final.Kernel.changedLookup (token , received) before changed reply (preparationKey token) accepted))

  finalKeepsPrefix : ∀ token received before →
    Store.lookupSaved (proj₁ (Final.execute (token , received) before)) token (preparationKey token) ≡
    Store.lookupSaved before token (preparationKey token)
  finalKeepsPrefix token received before with admitPublication (token , received) (Step.registration before)
  ... | just _ = refl
  ... | nothing with Store.lookupCancellation before token
  ... | just _ = refl
  ... | nothing with Store.lookupSaved before token (publicationKey token) | Store.lookupSaved before token Step.resultKey
  ... | just _ | just _ = refl
  ... | just _ | nothing = refl
  ... | nothing | just _ = refl
  ... | nothing | nothing with decidePublication (token , received) before in accepted
  ... | inj₁ _ = refl
  ... | inj₂ (changed , reply) = publishedPrefix token received before changed reply accepted

  second : PublicationObservation → ℕ → Store.World → Store.World × Step.Result G.Diagnostic
  second received token before with Store.lookupSaved before token (preparationKey token)
  ... | nothing = before , Step.needsRecovery
  ... | just _ = Final.execute (token , received) before
  secondStable : ∀ received token before → second received token (proj₁ (second received token before)) ≡ second received token before
  secondStable received token before with Store.lookupSaved before token (preparationKey token) in saved
  ... | nothing rewrite saved = refl
  ... | just _ rewrite finalKeepsPrefix token received before | saved = Final.stable (token , received) before
  secondPhysical : ∀ received token before → DB.Atomic before (proj₁ (second received token before))
    (Step.receiptFor (proj₂ (second received token before))) (proj₁ (second received token before))
  secondPhysical received token before with Store.lookupSaved before token (preparationKey token)
  ... | nothing = DB.abortedNone
  ... | just _ = Final.expectedPhysical (token , received) before

  module Run = Sequence.ObservedTwoPhases ℕ PreparationObservation PublicationObservation G.Diagnostic first second
    firstStable secondStable firstPhysical secondPhysical
    (λ token before → unavailable mismatch)
    (λ token before → publication (inj₁ (backendFault (toList "The operation requires its actual owned backend response."))) (serverTime token before))

  freshFirst : ∀ metadata token before changed reply → admit (token , metadata) (Step.registration before) ≡ nothing →
    Store.lookupCancellation before token ≡ nothing →
    Store.lookupSaved before token (preparationKey token) ≡ nothing →
    Store.lookupSaved before token (publicationKey token) ≡ nothing →
    Store.lookupSaved before token Step.resultKey ≡ nothing →
    decidePreparation (token , metadata) before ≡ inj₂ (changed , reply) →
    first metadata token before ≡ (Prefix.Base.firstPublication (token , metadata) changed reply , Step.done reply)
  freshFirst metadata token before changed reply admitted active firstMissing nextMissing resultMissing accepted
    rewrite admitted | active | firstMissing | nextMissing | resultMissing | accepted = refl

  FirstPublication : PreparationObservation → ℕ → Store.World → Set
  FirstPublication metadata token before = Σ Store.World (λ changed → Σ Wire.Value (λ reply →
    admit (token , metadata) (Step.registration before) ≡ nothing ×
    Store.lookupCancellation before token ≡ nothing ×
    Store.lookupSaved before token (preparationKey token) ≡ nothing ×
    Store.lookupSaved before token (publicationKey token) ≡ nothing ×
    Store.lookupSaved before token Step.resultKey ≡ nothing ×
    decidePreparation (token , metadata) before ≡ inj₂ (changed , reply)))

  firstClassification : ∀ metadata token before → (proj₁ (first metadata token before) ≡ before) ⊎ FirstPublication metadata token before
  firstClassification metadata token before with admit (token , metadata) (Step.registration before)
  ... | just _ = inj₁ refl
  ... | nothing with Store.lookupCancellation before token
  ... | just _ = inj₁ refl
  ... | nothing with Store.lookupSaved before token (preparationKey token) |
    Store.lookupSaved before token (publicationKey token) | Store.lookupSaved before token Step.resultKey
  ... | just _ | nothing | nothing = inj₁ refl
  ... | just _ | just _ | just _ = inj₁ refl
  ... | just _ | nothing | just _ = inj₁ refl
  ... | just _ | just _ | nothing = inj₁ refl
  ... | nothing | nothing | just _ = inj₁ refl
  ... | nothing | just _ | nothing = inj₁ refl
  ... | nothing | just _ | just _ = inj₁ refl
  ... | nothing | nothing | nothing with decidePreparation (token , metadata) before
  ... | inj₁ _ = inj₁ refl
  ... | inj₂ (changed , reply) = inj₂ (changed , reply , refl , refl , refl , refl , refl , refl)

  prefixPendingReplay : ∀ wanted token before saved → admit (token , wanted) (Step.registration before) ≡ nothing →
    Store.lookupCancellation before token ≡ nothing →
    Store.lookupSaved before token (preparationKey token) ≡ just saved →
    Store.lookupSaved before token (publicationKey token) ≡ nothing →
    Store.lookupSaved before token Step.resultKey ≡ nothing → first wanted token before ≡ (before , Step.done saved)
  prefixPendingReplay wanted token before saved admitted active firstSaved nextMissing resultMissing
    rewrite admitted | active | firstSaved | nextMissing | resultMissing = refl

  firstFamilyPreserved : ∀ wantedFirst wantedFinal received token before →
    Σ PreparationObservation (λ originalFirst → Σ PublicationObservation (λ originalFinal →
      Run.evaluate wantedFirst wantedFinal token (proj₁ (first received token before)) ≡
      Run.evaluate originalFirst originalFinal token before))
  firstFamilyPreserved wantedFirst wantedFinal received token before with firstClassification received token before
  ... | inj₁ same = wantedFirst , wantedFinal , cong (Run.evaluate wantedFirst wantedFinal token) same
  ... | inj₂ (changed , reply , admitted , active , firstMissing , nextMissing , resultMissing , accepted) =
    received , wantedFinal , trans
      (cong (λ outcome → Run.evaluate wantedFirst wantedFinal token (proj₁ outcome)) fresh)
      (trans (cong (λ outcome → Run.remaining wantedFinal token (proj₂ outcome) (proj₁ outcome)) replayed)
        (sym (cong (λ outcome → Run.remaining wantedFinal token (proj₂ outcome) (proj₁ outcome)) fresh)))
    where
    publishedWorld = Prefix.Base.firstPublication (token , received) changed reply
    fresh = freshFirst received token before changed reply admitted active firstMissing nextMissing resultMissing accepted
    stillAdmitted = trans (cong (admit (token , wantedFirst))
      (Prefix.keepsRegistration (token , received) before changed reply accepted)) admitted
    stillActive = trans (Prefix.keepsCancellation (token , received) before changed reply accepted) active
    stillNext = trans (Prefix.keepsNext (token , received) before changed reply accepted) nextMissing
    stillResult = Prefix.Base.firstHasNoResult (token , received) before changed reply accepted resultMissing
    firstReadable = Prefix.Base.firstReadable (token , received) before changed reply accepted firstMissing
    replayed = prefixPendingReplay wantedFirst token publishedWorld reply stillAdmitted stillActive firstReadable stillNext stillResult

  secondFresh : ∀ received token before saved changed reply →
    Store.lookupSaved before token (preparationKey token) ≡ just saved →
    admitPublication (token , received) (Step.registration before) ≡ nothing →
    Store.lookupCancellation before token ≡ nothing →
    Store.lookupSaved before token (publicationKey token) ≡ nothing → Store.lookupSaved before token Step.resultKey ≡ nothing →
    decidePublication (token , received) before ≡ inj₂ (changed , reply) →
    second received token before ≡ (Final.Kernel.publication (token , received) changed reply , Step.done reply)
  secondFresh received token before saved changed reply firstSaved admitted active finalMissing resultMissing accepted
    rewrite firstSaved | admitted | active | finalMissing | resultMissing | accepted = refl

  prefixCompletedReplay : ∀ wanted token before saved final result →
    admit (token , wanted) (Step.registration before) ≡ nothing → Store.lookupCancellation before token ≡ nothing →
    Store.lookupSaved before token (preparationKey token) ≡ just saved →
    Store.lookupSaved before token (publicationKey token) ≡ just final → Store.lookupSaved before token Step.resultKey ≡ just result →
    first wanted token before ≡ (before , Step.done saved)
  prefixCompletedReplay wanted token before saved final result admitted active firstSaved finalSaved resultSaved
    rewrite admitted | active | firstSaved | finalSaved | resultSaved = refl

  secondCompletedReplay : ∀ wanted token before first final result →
    Store.lookupSaved before token (preparationKey token) ≡ just first →
    admitPublication (token , wanted) (Step.registration before) ≡ nothing → Store.lookupCancellation before token ≡ nothing →
    Store.lookupSaved before token (publicationKey token) ≡ just final → Store.lookupSaved before token Step.resultKey ≡ just result →
    second wanted token before ≡ (before , Step.done final)
  secondCompletedReplay wanted token before first final result firstSaved admitted active finalSaved resultSaved
    rewrite firstSaved | admitted | active | finalSaved | resultSaved = refl

  publishedEvaluation : ∀ initial wanted received token before saved changed reply →
    Store.lookupSaved before token (preparationKey token) ≡ just saved →
    admitPublication (token , received) (Step.registration before) ≡ nothing → Store.lookupCancellation before token ≡ nothing →
    Store.lookupSaved before token (publicationKey token) ≡ nothing → Store.lookupSaved before token Step.resultKey ≡ nothing →
    decidePublication (token , received) before ≡ inj₂ (changed , reply) →
    Run.evaluate initial wanted token (Final.Kernel.publication (token , received) changed reply) ≡
      (Final.Kernel.publication (token , received) changed reply , Step.done reply)
  publishedEvaluation initial wanted received token before saved changed reply firstSaved admitted active finalMissing resultMissing accepted = trans
    (cong (λ outcome → Run.remaining wanted token (proj₂ outcome) (proj₁ outcome)) prefixReplayed)
    (secondCompletedReplay wanted token finalWorld saved reply reply firstReadable finalAdmitted stillActive finalReadable resultReadable)
    where
    finalWorld = Final.Kernel.publication (token , received) changed reply
    registration = Final.Kernel.publicationKeepsRegistration (token , received) before changed reply accepted
    prefixAdmitted = trans (cong (admit (token , initial)) registration) admitted
    finalAdmitted = trans (cong (admitPublication (token , wanted)) registration) admitted
    stillActive = trans (Final.Kernel.publicationKeepsCancellation (token , received) before changed reply accepted) active
    firstReadable = trans (publishedPrefix token received before changed reply accepted) firstSaved
    finalReadable = Final.Kernel.publishedStepReadable (token , received) before changed reply accepted finalMissing
    resultReadable = Final.Kernel.publishedResultReadable (token , received) before changed reply accepted resultMissing
    prefixReplayed = prefixCompletedReplay initial token finalWorld saved reply reply prefixAdmitted stillActive firstReadable finalReadable resultReadable

  originalEvaluation : ∀ initial received token before saved changed reply →
    Store.lookupSaved before token (preparationKey token) ≡ just saved →
    admitPublication (token , received) (Step.registration before) ≡ nothing → Store.lookupCancellation before token ≡ nothing →
    Store.lookupSaved before token (publicationKey token) ≡ nothing → Store.lookupSaved before token Step.resultKey ≡ nothing →
    decidePublication (token , received) before ≡ inj₂ (changed , reply) →
    Run.evaluate initial received token before ≡ (Final.Kernel.publication (token , received) changed reply , Step.done reply)
  originalEvaluation initial received token before saved changed reply firstSaved admitted active finalMissing resultMissing accepted = trans
    (cong (λ outcome → Run.remaining received token (proj₂ outcome) (proj₁ outcome))
      (prefixPendingReplay initial token before saved admitted active firstSaved finalMissing resultMissing))
    (secondFresh received token before saved changed reply firstSaved admitted active finalMissing resultMissing accepted)

  SecondPublication : PublicationObservation → ℕ → Store.World → Set
  SecondPublication received token before = Σ Wire.Value (λ saved → Σ Store.World (λ changed → Σ Wire.Value (λ reply →
    Store.lookupSaved before token (preparationKey token) ≡ just saved ×
    admitPublication (token , received) (Step.registration before) ≡ nothing × Store.lookupCancellation before token ≡ nothing ×
    Store.lookupSaved before token (publicationKey token) ≡ nothing × Store.lookupSaved before token Step.resultKey ≡ nothing ×
    decidePublication (token , received) before ≡ inj₂ (changed , reply))))

  secondClassification : ∀ received token before → (proj₁ (second received token before) ≡ before) ⊎ SecondPublication received token before
  secondClassification received token before with Store.lookupSaved before token (preparationKey token)
  ... | nothing = inj₁ refl
  ... | just saved with admitPublication (token , received) (Step.registration before)
  ... | just _ = inj₁ refl
  ... | nothing with Store.lookupCancellation before token
  ... | just _ = inj₁ refl
  ... | nothing with Store.lookupSaved before token (publicationKey token) | Store.lookupSaved before token Step.resultKey
  ... | just _ | just _ = inj₁ refl
  ... | just _ | nothing = inj₁ refl
  ... | nothing | just _ = inj₁ refl
  ... | nothing | nothing with decidePublication (token , received) before
  ... | inj₁ _ = inj₁ refl
  ... | inj₂ (changed , reply) = inj₂ (saved , changed , reply , refl , refl , refl , refl , refl , refl)

  secondKeepsFamily : ∀ initial wanted received token before → Σ PublicationObservation (λ original →
    Run.evaluate initial wanted token (proj₁ (second received token before)) ≡ Run.evaluate initial original token before)
  secondKeepsFamily initial wanted received token before with secondClassification received token before
  ... | inj₁ same = wanted , cong (Run.evaluate initial wanted token) same
  ... | inj₂ (saved , changed , reply , firstSaved , admitted , active , finalMissing , resultMissing , accepted) = received , trans
    (cong (Run.evaluate initial wanted token)
      (cong proj₁ (secondFresh received token before saved changed reply firstSaved admitted active finalMissing resultMissing accepted)))
    (trans (publishedEvaluation initial wanted received token before saved changed reply firstSaved admitted active finalMissing resultMissing accepted)
      (sym (originalEvaluation initial received token before saved changed reply firstSaved admitted active finalMissing resultMissing accepted)))

  PreparationIntent : ℕ → PreparationObservation → Request → Store.World → G.Outcome → Set
  PreparationIntent token (unavailable fault) actual before outcome = outcome ≡ inj₁ (G.requestFault fault)
  PreparationIntent token (observed input metadata snapshot value captured serialized) actual before outcome with sameRequest actual input
  ... | false = outcome ≡ inj₁ (G.requestFault mismatch)
  ... | true with capture input metadata before
  ... | inj₁ fault = outcome ≡ inj₁ (G.requestFault fault)
  ... | inj₂ capturedValue = outcome ≡ inj₂ (addOwner token metadata (Request.project actual) before , C.encode capturedValue)

  preparationMeaning : ∀ token metadata actual before → PreparationIntent token metadata actual before (prepare token metadata actual before)
  preparationMeaning token (unavailable fault) actual before = refl
  preparationMeaning token (observed input metadata snapshot value captured serialized) actual before with sameRequest actual input
  ... | false = refl
  ... | true with capture input metadata before
  ... | inj₁ fault = refl
  ... | inj₂ capturedValue = refl

  FreshPreparationGoal : ℕ → PreparationObservation → Request → Store.World → Store.World → Run.Value → Set
  FreshPreparationGoal token metadata actual before after (Step.done reply) = Σ Store.World (λ owned →
    PreparationIntent token metadata actual before (inj₂ (owned , reply)) ×
    after ≡ Prefix.Base.firstPublication (token , metadata) owned reply)
  FreshPreparationGoal token metadata actual before after (Step.needsInput diagnostic) =
    after ≡ before × PreparationIntent token metadata actual before (inj₁ diagnostic)
  FreshPreparationGoal token metadata actual before after _ = ⊥

  prepareOriginal : ∀ token metadata actual before → original token (Step.registration before) ≡ inj₂ actual →
    decidePreparation (token , metadata) before ≡ prepare token metadata actual before
  prepareOriginal token metadata actual before bound rewrite bound = refl

  freshPreparationMeaning : ∀ token metadata actual before → original token (Step.registration before) ≡ inj₂ actual →
    FreshPreparationGoal token metadata actual before (proj₁ (Prefix.fresh (token , metadata) before)) (proj₂ (Prefix.fresh (token , metadata) before))
  freshPreparationMeaning token metadata actual before bound rewrite prepareOriginal token metadata actual before bound
    with prepare token metadata actual before | preparationMeaning token metadata actual before
  ... | inj₁ diagnostic | correct = refl , correct
  ... | inj₂ (owned , reply) | correct = owned , correct , refl

  FirstGoal : ℕ → PreparationObservation → Store.World → Store.World → Run.Value → Set
  FirstGoal token metadata before after reply with original token (Step.registration before)
  ... | inj₁ fault = after ≡ before × reply ≡ Step.needsInput (G.requestFault fault)
  ... | inj₂ actual with Store.lookupCancellation before token
  ... | just cancelled = after ≡ before × reply ≡ Step.cancelled cancelled
  ... | nothing with Store.lookupSaved before token (preparationKey token) |
    Store.lookupSaved before token (publicationKey token) | Store.lookupSaved before token Step.resultKey
  ... | just saved | nothing | nothing = after ≡ before × reply ≡ Step.done saved
  ... | just saved | just _ | just _ = after ≡ before × reply ≡ Step.done saved
  ... | just _ | nothing | just _ = after ≡ before × reply ≡ Step.needsRecovery
  ... | just _ | just _ | nothing = after ≡ before × reply ≡ Step.needsRecovery
  ... | nothing | nothing | just _ = after ≡ before × reply ≡ Step.needsRecovery
  ... | nothing | just _ | nothing = after ≡ before × reply ≡ Step.needsRecovery
  ... | nothing | just _ | just _ = after ≡ before × reply ≡ Step.needsRecovery
  ... | nothing | nothing | nothing = FreshPreparationGoal token metadata actual before after reply

  firstMeaning : ∀ metadata token before → FirstGoal token metadata before (proj₁ (first metadata token before)) (proj₂ (first metadata token before))
  firstMeaning metadata token before with original token (Step.registration before) in bound
  ... | inj₁ fault = refl , refl
  ... | inj₂ actual with Store.lookupCancellation before token
  ... | just cancelled = refl , refl
  ... | nothing with Store.lookupSaved before token (preparationKey token) |
    Store.lookupSaved before token (publicationKey token) | Store.lookupSaved before token Step.resultKey
  ... | just saved | nothing | nothing = refl , refl
  ... | just saved | just _ | just _ = refl , refl
  ... | just _ | nothing | just _ = refl , refl
  ... | just _ | just _ | nothing = refl , refl
  ... | nothing | nothing | just _ = refl , refl
  ... | nothing | just _ | nothing = refl , refl
  ... | nothing | just _ | just _ = refl , refl
  ... | nothing | nothing | nothing = freshPreparationMeaning token metadata actual before bound

  PublicationIntent : ℕ → PublicationObservation → Request → Store.World → G.Outcome → Set
  PublicationIntent token received actual before outcome with storedPreparation token before
  ... | inj₁ fault = outcome ≡ inj₁ (G.requestFault fault)
  ... | inj₂ value with sameProject (Request.project actual) (Prepared.project value) ∧
    hasOwner token value (Store.World.embeddingOwners before) ∧
    sameChunks (documentRows (Prepared.path value) before) (Prepared.previous value)
  ... | false = outcome ≡ inj₁ (G.requestFault stale)
  ... | true = PreparedGoal token value received before outcome

  publicationMeaning : ∀ token received actual before → original token (Step.registration before) ≡ inj₂ actual →
    PublicationIntent token received actual before (decidePublication (token , received) before)
  publicationMeaning token received actual before bound rewrite bound with storedPreparation token before
  ... | inj₁ fault = refl
  ... | inj₂ value with sameProject (Request.project actual) (Prepared.project value) ∧
    hasOwner token value (Store.World.embeddingOwners before) ∧
    sameChunks (documentRows (Prepared.path value) before) (Prepared.previous value)
  ... | false = refl
  ... | true = calculateMeaning token value received before

  FreshPublicationGoal : ℕ → PublicationObservation → Request → Store.World → Store.World → Run.Value → Set
  FreshPublicationGoal token received actual before after (Step.done reply) = Σ Store.World (λ replaced →
    PublicationIntent token received actual before (inj₂ (replaced , reply)) ×
    after ≡ Final.Kernel.publication (token , received) replaced reply)
  FreshPublicationGoal token received actual before after (Step.needsInput diagnostic) =
    after ≡ before × PublicationIntent token received actual before (inj₁ diagnostic)
  FreshPublicationGoal token received actual before after _ = ⊥

  freshPublicationMeaning : ∀ token received actual before → original token (Step.registration before) ≡ inj₂ actual →
    FreshPublicationGoal token received actual before (proj₁ (Final.Kernel.fresh (token , received) before)) (proj₂ (Final.Kernel.fresh (token , received) before))
  freshPublicationMeaning token received actual before bound with decidePublication (token , received) before | publicationMeaning token received actual before bound
  ... | inj₁ diagnostic | correct = refl , correct
  ... | inj₂ (replaced , reply) | correct = replaced , correct , refl

  FinalGoal : ℕ → PublicationObservation → Store.World → Store.World → Run.Value → Set
  FinalGoal token received before after reply with Store.lookupSaved before token (preparationKey token)
  ... | nothing = after ≡ before × reply ≡ Step.needsRecovery
  ... | just saved with original token (Step.registration before)
  ... | inj₁ fault = after ≡ before × reply ≡ Step.needsInput (G.requestFault fault)
  ... | inj₂ actual with Store.lookupCancellation before token
  ... | just cancelled = after ≡ before × reply ≡ Step.cancelled cancelled
  ... | nothing with Store.lookupSaved before token (publicationKey token) | Store.lookupSaved before token Step.resultKey
  ... | just final | just _ = after ≡ before × reply ≡ Step.done final
  ... | just _ | nothing = after ≡ before × reply ≡ Step.needsRecovery
  ... | nothing | just _ = after ≡ before × reply ≡ Step.needsRecovery
  ... | nothing | nothing = FreshPublicationGoal token received actual before after reply

  finalMeaning : ∀ received token before → FinalGoal token received before (proj₁ (second received token before)) (proj₂ (second received token before))
  finalMeaning received token before with Store.lookupSaved before token (preparationKey token)
  ... | nothing = refl , refl
  ... | just saved with original token (Step.registration before) in bound
  ... | inj₁ fault = refl , refl
  ... | inj₂ actual with Store.lookupCancellation before token
  ... | just cancelled = refl , refl
  ... | nothing with Store.lookupSaved before token (publicationKey token) | Store.lookupSaved before token Step.resultKey
  ... | just final | just _ = refl , refl
  ... | just _ | nothing = refl , refl
  ... | nothing | just _ = refl , refl
  ... | nothing | nothing = freshPublicationMeaning token received actual before bound

  ContinuationGoal : ℕ → PublicationObservation → Store.World → Run.Value → Store.World → Run.Value → Set
  ContinuationGoal token received middle (Step.done _) after reply = FinalGoal token received middle after reply
  ContinuationGoal token received middle previous after reply = after ≡ middle × reply ≡ previous

  Goal : ℕ → Store.World → Store.World → Run.Value → Set
  Goal token before after reply = Σ PreparationObservation (λ initial → Σ PublicationObservation (λ received →
    Σ Store.World (λ middle → Σ Run.Value (λ previous →
      FirstGoal token initial before middle previous × ContinuationGoal token received middle previous after reply))))

  meaning : ∀ initial received token before → Goal token before
    (proj₁ (Run.evaluate initial received token before)) (proj₂ (Run.evaluate initial received token before))
  meaning initial received token before with first initial token before | firstMeaning initial token before
  ... | middle , Step.done previous | correct = initial , received , middle , Step.done previous , correct , finalMeaning received token middle
  ... | middle , Step.needsInput diagnostic | correct = initial , received , middle , Step.needsInput diagnostic , correct , refl , refl
  ... | middle , Step.needsRecovery | correct = initial , received , middle , Step.needsRecovery , correct , refl , refl
  ... | middle , Step.cancelled cancelled | correct = initial , received , middle , Step.cancelled cancelled , correct , refl , refl

  private
    module Certified = Run.Certified firstFamilyPreserved secondKeepsFamily Goal meaning

  -- This fixed public protocol owns the source and provider observations.
  -- Its caller supplies only a token, never a prepared document or vector.
  module Public (coreConfiguration : Config.Config) where
    configuration : Maybe Config.Embeddings
    configuration = Config.Config.embed coreConfiguration
    module Identity = Project.Registered
    identityMatches : Config.Embeddings → Wire.Value → Bool
    identityMatches cfg with Config.Embeddings.backend cfg
    ... | Config.local = Belief.ProviderSettings.local
    ... | Config.voyage = Identity.fields (toList "backend" ∷ toList "model" ∷ toList "input_type" ∷ toList "truncation" ∷ []) λ view →
      Identity.fieldText (toList "voyage") (view (toList "backend")) ∧
      Identity.fieldText (Config.Embeddings.model cfg) (view (toList "model")) ∧
      Identity.fieldText (toList "document") (view (toList "input_type")) ∧ Identity.fieldFalse (view (toList "truncation"))
    ... | Config.openai = Identity.fields (toList "backend" ∷ toList "model" ∷ []) λ view →
      Identity.fieldText (toList "openai") (view (toList "backend")) ∧
      Identity.fieldText (Config.Embeddings.model cfg) (view (toList "model"))
    configuredIdentity : Config.Embeddings → Maybe Wire.Value → Bool
    configuredIdentity cfg nothing = false
    configuredIdentity cfg (just value) = identityMatches cfg value
    settingsMatch : Config.Embeddings → ℕ → Store.World → Bool
    settingsMatch cfg token snapshot with Identity.binding token (Store.OperationTables.bindings (Store.World.operations snapshot))
    ... | nothing = false
    ... | just bound = Identity.fields (toList "embeddings" ∷ [])
      (λ view → configuredIdentity cfg (view (toList "embeddings"))) (Store.BindingRow.settings bound)

    PreparationEvidence : ℕ → Store.World → PreparationObservation → Set
    PreparationEvidence token before (unavailable fault) = ⊤
    PreparationEvidence token before (observed input metadata snapshot value captured serialized) =
      snapshot ≡ before × Σ Request (λ actual → original token (Step.registration before) ≡ inj₂ actual ×
        Σ (List FileObservation.E.Event) (λ events →
          FileObservation.E.Runs (FileObservation.script (Request.path actual) (Request.project actual)) events (inj₂ input)) ×
        Σ Config.Embeddings (λ cfg → configuration ≡ just cfg × settingsMatch cfg token before ≡ true))

    data Effect : Set where
      reserve readSources : ℕ → Effect
      embed : ℕ → Config.Embeddings → List Text → Effect
      publish : ℕ → Validation.Fault ⊎ List Store.Vector → Effect
    Reply : Effect → Set
    Reply (reserve _) = PreparationObservation × Run.Value
    Reply (readSources _) = Validation.Fault ⊎ Store.World
    Reply (embed _ _ _) = Text ⊎ List Store.Vector
    Reply (publish _ _) = ℤ × Run.Value
    module E = Effects.Protocol Effect Reply
    record Result : Set where
      constructor completed
      field value : Run.Value; transcript : List E.Event

    missingBackend : Validation.Fault
    missingBackend = Validation.fault (Validation.key "embeddings" ∷ []) Validation.missingField
      "Document indexing needs an embedding backend. Configure one or ask the user before cancelling this unfinished operation; the previous index was not replaced."
    changedBackend : Validation.Fault
    changedBackend = Validation.fault (Validation.key "embeddings" ∷ []) Validation.wrongIdentity
      "The configured embedding backend differs from the original operation. Read the original binding and outcome; ask the user before cancellation and a corrected reservation. The previous index was not replaced."
    providerResult : Text ⊎ List Store.Vector → Validation.Fault ⊎ List Store.Vector
    providerResult (inj₁ reason) = inj₁ (backendFault reason)
    providerResult (inj₂ vectors) = inj₂ vectors
    finish : ℕ → List E.Event → Validation.Fault ⊎ List Store.Vector → E.Script Result
    finish token previous vectors = E.ask (publish token vectors) (λ observation →
      E.done (completed (proj₂ observation) (previous ++ ((publish token vectors , observation) ∷ []))))
    afterInput : ℕ → List E.Event → Store.World → Validation.Fault ⊎ Prepared → E.Script Result
    afterInput token previous snapshot (inj₁ fault) = finish token previous (inj₁ fault)
    afterInput token previous snapshot (inj₂ value) with configuration
    ... | nothing = finish token previous (inj₁ missingBackend)
    ... | just cfg with settingsMatch cfg token snapshot
    ... | false = finish token previous (inj₁ changedBackend)
    ... | true with Prepared.chunks value
    ... | [] = finish token previous (inj₂ [])
    ... | _ ∷ _ = E.ask (embed token cfg (map Documents.Chunk.content (Prepared.chunks value))) (λ response →
      finish token (previous ++ ((embed token cfg (map Documents.Chunk.content (Prepared.chunks value)) , response) ∷ [])) (providerResult response))
    afterSnapshot : ℕ → List E.Event → Validation.Fault ⊎ Store.World → E.Script Result
    afterSnapshot token previous (inj₁ fault) = finish token previous (inj₁ fault)
    afterSnapshot token previous (inj₂ snapshot) with Store.lookupSaved snapshot token (publicationKey token)
      | Store.lookupSaved snapshot token Step.resultKey
    ... | nothing | nothing = afterInput token previous snapshot (storedPreparation token snapshot)
    ... | just _ | _ = finish token previous (inj₁ mismatch)
    ... | nothing | just _ = finish token previous (inj₁ mismatch)
    afterOwner : ℕ → List E.Event → Run.Value → E.Script Result
    afterOwner token previous (Step.done _) = E.ask (readSources token) (λ observation →
      afterSnapshot token (previous ++ ((readSources token , observation) ∷ [])) observation)
    afterOwner token previous value@(Step.needsInput _) = E.done (completed value previous)
    afterOwner token previous Step.needsRecovery = E.done (completed Step.needsRecovery previous)
    afterOwner token previous value@(Step.cancelled _) = E.done (completed value previous)
    script : ℕ → E.Script Result
    script token = E.ask (reserve token) (λ observation → afterOwner token ((reserve token , observation) ∷ []) (proj₂ observation))
    Atomic : Store.World → (effect : Effect) → Reply effect → Store.World → Set
    Atomic before (reserve token) (metadata , value) after =
      Run.Atomic before (Run.prefix token) (metadata , value) after × PreparationEvidence token before metadata
    Atomic before (readSources token) (inj₁ reason) after = after ≡ before
    Atomic before (readSources token) (inj₂ snapshot) after = snapshot ≡ before × after ≡ before
    Atomic before (embed token cfg content) reply after = after ≡ before
    Atomic before (publish token vectors) (time , value) after =
      Run.Atomic before (Run.finish token) (publication vectors time , value) after
    module X = Recovery.Execution Store.World Effect Reply Atomic

    data Owned (token : ℕ) : Effect → Set where
      ownerOwned : Owned token (reserve token)
      sourcesOwned : Owned token (readSources token)
      embedOwned : ∀ cfg content → Owned token (embed token cfg content)
      publishOwned : ∀ observation → Owned token (publish token observation)

    data Scoped (token : ℕ) : E.Script Result → Set where
      returned : ∀ value → Scoped token (E.done value)
      asked : ∀ effect continuation → Owned token effect →
        (∀ reply → Scoped token (continuation reply)) → Scoped token (E.ask effect continuation)

    finishScoped : ∀ token previous observation → Scoped token (finish token previous observation)
    finishScoped token previous observation = asked _ _ (publishOwned observation) (λ value → returned _)
    inputScoped : ∀ token previous snapshot input → Scoped token (afterInput token previous snapshot input)
    inputScoped token previous snapshot (inj₁ fault) = finishScoped _ _ _
    inputScoped token previous snapshot (inj₂ value) with configuration
    ... | nothing = finishScoped _ _ _
    ... | just cfg with settingsMatch cfg token snapshot
    ... | false = finishScoped _ _ _
    ... | true with Prepared.chunks value
    ... | [] = finishScoped _ _ _
    ... | _ ∷ _ = asked _ _ (embedOwned cfg (map Documents.Chunk.content (Prepared.chunks value))) (λ response → finishScoped _ _ _)
    snapshotScoped : ∀ token previous observation → Scoped token (afterSnapshot token previous observation)
    snapshotScoped token previous (inj₁ fault) = finishScoped _ _ _
    snapshotScoped token previous (inj₂ snapshot) with Store.lookupSaved snapshot token (publicationKey token)
      | Store.lookupSaved snapshot token Step.resultKey
    ... | nothing | nothing = inputScoped token previous snapshot (storedPreparation token snapshot)
    ... | just _ | _ = finishScoped _ _ _
    ... | nothing | just _ = finishScoped _ _ _
    ownerScoped : ∀ token previous value → Scoped token (afterOwner token previous value)
    ownerScoped token previous (Step.done _) = asked _ _ sourcesOwned (λ snapshot →
      snapshotScoped token (previous ++ ((readSources token , snapshot) ∷ [])) snapshot)
    ownerScoped token previous (Step.needsInput _) = returned _
    ownerScoped token previous Step.needsRecovery = returned _
    ownerScoped token previous (Step.cancelled _) = returned _
    scriptScoped : ∀ token → Scoped token (script token)
    scriptScoped token = asked _ _ ownerOwned (λ observation → ownerScoped _ _ _)

    prefixScoped : ∀ token program events residual → Scoped token program → E.Prefix program events residual →
      All (λ event → Owned token (proj₁ event)) events × Scoped token residual
    prefixScoped token program [] .program scoped (E.stopped _) = [] , scoped
    prefixScoped token .(E.ask effect continuation) .((effect , reply) ∷ events) residual
      (asked effect continuation own later) (E.replied _ _ reply {events} rest)
      with prefixScoped token (continuation reply) events residual (later reply) rest
    ... | owners , scoped = (own ∷ owners) , scoped
    activeOwned : ∀ token effect continuation → Scoped token (E.ask effect continuation) → Owned token effect
    activeOwned token effect continuation (asked .effect .continuation own later) = own

    atomicInvariant : ∀ token initial before after effect reply → Owned token effect →
      Atomic before effect reply after → Certified.Invariant token initial before → Certified.Invariant token initial after
    atomicInvariant token initial before after .(reserve token) observation ownerOwned physical invariant =
      Certified.atomicInvariant token initial before after (Run.prefix token) observation Run.firstOwned (proj₁ physical) invariant
    atomicInvariant token initial before .before .(readSources token) (inj₁ reason) sourcesOwned refl invariant = invariant
    atomicInvariant token initial before .before .(readSources token) (inj₂ .before) sourcesOwned (refl , refl) invariant = invariant
    atomicInvariant token initial before .before .(embed token cfg content) reply (embedOwned cfg content) refl invariant = invariant
    atomicInvariant token initial before after .(publish token observation) (time , reply) (publishOwned observation) physical invariant =
      Certified.atomicInvariant token initial before after (Run.finish token) (publication observation time , reply) Run.secondOwned physical invariant

    changesInvariant : ∀ token initial before events after → All (λ event → Owned token (proj₁ event)) events →
      X.Changes before events after → Certified.Invariant token initial before → Certified.Invariant token initial after
    changesInvariant token initial before [] .before [] (X.unchanged _) old = old
    changesInvariant token initial before ((effect , reply) ∷ events) after (own ∷ owners)
      (X.changed _ _ _ middle physical rest) old = changesInvariant token initial middle events after owners rest
        (atomicInvariant token initial before middle effect reply own physical old)

    interruptedInvariant : ∀ token initial interrupted → X.Interrupted (script token) initial interrupted → Certified.Invariant token initial interrupted
    interruptedInvariant token initial interrupted (X.atPrefix events residual .interrupted prefix physical) =
      changesInvariant token initial initial events interrupted
        (proj₁ (prefixScoped token (script token) events residual (scriptScoped token) prefix)) physical
        (λ first final → first , final , refl)
    interruptedInvariant token initial interrupted
      (X.beforeReply events effect continuation current reply .interrupted prefix physical active)
      with prefixScoped token (script token) events (E.ask effect continuation) (scriptScoped token) prefix
    ... | owners , residual = atomicInvariant token initial current interrupted effect reply
      (activeOwned token effect continuation residual) active
      (changesInvariant token initial initial events current owners physical (λ first final → first , final , refl))

    finishObservation : ∀ token previous vectors before after result events →
      E.Runs (finish token previous vectors) events result → X.Changes before events after →
      Σ PublicationObservation (λ observation → (after , Result.value result) ≡ second observation token before)
    finishObservation token previous vectors before after ._ ._
      (E.replied _ _ (time , reply) (E.returned _)) (X.changed _ _ _ _ physical (X.unchanged _)) =
      publication vectors time , Run.Second.atomicObservation (publication vectors time) token before after reply physical
    inputObservation : ∀ token previous snapshot input before after result events →
      E.Runs (afterInput token previous snapshot input) events result → X.Changes before events after →
      Σ PublicationObservation (λ observation → (after , Result.value result) ≡ second observation token before)
    inputObservation token previous snapshot (inj₁ fault) before after result events execution physical =
      finishObservation token previous _ before after result events execution physical
    inputObservation token previous snapshot (inj₂ value) before after result events execution physical with configuration
    ... | nothing = finishObservation token previous _ before after result events execution physical
    ... | just cfg with settingsMatch cfg token snapshot
    ... | false = finishObservation token previous _ before after result events execution physical
    ... | true with Prepared.chunks value
    ... | [] = finishObservation token previous _ before after result events execution physical
    inputObservation token previous snapshot (inj₂ value) before after result ._
      (E.replied _ _ response execution) (X.changed _ _ _ .before refl physical) | just cfg | true | _ ∷ _ =
      finishObservation token _ (providerResult response) before after result _ execution physical
    snapshotObservation : ∀ token previous observation before after result events →
      E.Runs (afterSnapshot token previous observation) events result → X.Changes before events after →
      Σ PublicationObservation (λ observation → (after , Result.value result) ≡ second observation token before)
    snapshotObservation token previous (inj₁ fault) before after result events execution physical =
      finishObservation token previous _ before after result events execution physical
    snapshotObservation token previous (inj₂ snapshot) before after result events execution physical
      with Store.lookupSaved snapshot token (publicationKey token) | Store.lookupSaved snapshot token Step.resultKey
    ... | nothing | nothing = inputObservation token previous snapshot (storedPreparation token snapshot) before after result events execution physical
    ... | just _ | _ = finishObservation token previous _ before after result events execution physical
    ... | nothing | just _ = finishObservation token previous _ before after result events execution physical

    sourceReadUnchanged : ∀ token before reply after → Atomic before (readSources token) reply after → after ≡ before
    sourceReadUnchanged token before (inj₁ reason) after physical = physical
    sourceReadUnchanged token before (inj₂ snapshot) after physical = proj₂ physical

    tailObservation : ∀ token previous value before after result events →
      E.Runs (afterOwner token previous value) events result → X.Changes before events after →
      Σ PublicationObservation (λ observation → (after , Result.value result) ≡ Run.remaining observation token value before)
    tailObservation token previous (Step.done _) before after result ._
      (E.replied _ _ snapshot execution) (X.changed _ _ _ middle read physical)
      with snapshotObservation token _ snapshot middle after result _ execution physical
    ... | observation , same = observation , trans same
      (cong (second observation token) (sourceReadUnchanged token before snapshot middle read))
    tailObservation token previous (Step.needsInput diagnostic) before .before ._ .[] (E.returned _) (X.unchanged _) = publication (inj₁ mismatch) (serverTime token before) , refl
    tailObservation token previous Step.needsRecovery before .before ._ .[] (E.returned _) (X.unchanged _) = publication (inj₁ mismatch) (serverTime token before) , refl
    tailObservation token previous (Step.cancelled cancelled) before .before ._ .[] (E.returned _) (X.unchanged _) = publication (inj₁ mismatch) (serverTime token before) , refl

    completedObservation : ∀ token before after result → X.Completed (script token) before after result →
      Σ PreparationObservation (λ metadata → Σ PublicationObservation (λ observation →
        (after , Result.value result) ≡ Run.evaluate metadata observation token before))
    completedObservation token before after result
      (X.completed _ (E.replied _ _ (metadata , previous) execution) (X.changed _ _ _ middle physical rest))
      with tailObservation token _ previous middle after result _ execution rest
    ... | observation , same = metadata , observation , trans same
      (cong (λ pair → Run.remaining observation token (proj₂ pair) (proj₁ pair))
        (Run.First.atomicObservation metadata token before middle previous (proj₁ physical)))

    PublicGoal : ℕ → Store.World → Store.World → Result → Set
    PublicGoal token before after result = Goal token before after (Result.value result)

    converges : ∀ token initial interrupted after result → X.Interrupted (script token) initial interrupted →
      X.Completed (script token) interrupted after result → PublicGoal token initial after result
    converges token initial interrupted after result crash completion
      with completedObservation token interrupted after result completion
    ... | metadata , observation , same with interruptedInvariant token initial interrupted crash metadata observation
    ... | original , final , retained = subst
      (λ pair → Goal token initial (proj₁ pair) (proj₂ pair)) (sym (trans same retained)) (meaning original final token initial)

    finishProgress : ∀ token previous vectors before → Σ Store.World (λ after → Σ Result (λ result →
      X.Completed (finish token previous vectors) before after result))
    finishProgress token previous vectors before = proj₁ proposed , result , X.completed
      ((publish token vectors , (time , proj₂ proposed)) ∷ []) (E.replied _ _ _ (E.returned _))
      (X.changed before _ _ _ (refl , secondPhysical received token before) (X.unchanged _))
      where
      time = serverTime token before
      received = publication vectors time
      proposed = second received token before
      result = completed (proj₂ proposed) (previous ++ ((publish token vectors , (time , proj₂ proposed)) ∷ []))
    inputProgress : ∀ token previous snapshot input before → Σ Store.World (λ after → Σ Result (λ result →
      X.Completed (afterInput token previous snapshot input) before after result))
    inputProgress token previous snapshot (inj₁ fault) before = finishProgress _ _ _ _
    inputProgress token previous snapshot (inj₂ value) before with configuration
    ... | nothing = finishProgress _ _ _ _
    ... | just cfg with settingsMatch cfg token snapshot
    ... | false = finishProgress _ _ _ _
    ... | true with Prepared.chunks value
    ... | [] = finishProgress _ _ _ _
    ... | _ ∷ _ with finishProgress token
      (previous ++ ((embed token cfg (map Documents.Chunk.content (Prepared.chunks value)) , inj₁ []) ∷ []))
      (providerResult (inj₁ [])) before
    ... | after , result , X.completed events execution physical = after , result , X.completed
      ((embed token cfg (map Documents.Chunk.content (Prepared.chunks value)) , inj₁ []) ∷ events) (E.replied _ _ _ execution)
      (X.changed before _ _ before refl physical)
    snapshotProgress : ∀ token previous observation before → Σ Store.World (λ after → Σ Result (λ result →
      X.Completed (afterSnapshot token previous observation) before after result))
    snapshotProgress token previous (inj₁ fault) before = finishProgress _ _ _ _
    snapshotProgress token previous (inj₂ snapshot) before
      with Store.lookupSaved snapshot token (publicationKey token) | Store.lookupSaved snapshot token Step.resultKey
    ... | nothing | nothing = inputProgress token previous snapshot (storedPreparation token snapshot) before
    ... | just _ | _ = finishProgress _ _ _ _
    ... | nothing | just _ = finishProgress _ _ _ _

    ownerProgress : ∀ token previous value before → Σ Store.World (λ after → Σ Result (λ result →
      X.Completed (afterOwner token previous value) before after result))
    ownerProgress token previous (Step.done _) before with snapshotProgress token
      (previous ++ ((readSources token , inj₂ before) ∷ [])) (inj₂ before) before
    ... | after , result , X.completed events execution physical = after , result , X.completed
      ((readSources token , inj₂ before) ∷ events) (E.replied _ _ _ execution)
      (X.changed before _ _ before (refl , refl) physical)
    ownerProgress token previous (Step.needsInput diagnostic) before = before , completed (Step.needsInput diagnostic) previous ,
      X.completed [] (E.returned _) (X.unchanged _)
    ownerProgress token previous Step.needsRecovery before = before , completed Step.needsRecovery previous ,
      X.completed [] (E.returned _) (X.unchanged _)
    ownerProgress token previous (Step.cancelled cancelled) before = before , completed (Step.cancelled cancelled) previous ,
      X.completed [] (E.returned _) (X.unchanged _)

    -- Existence of an allowed external response does not assert provider
    -- success or determinism, and introduces no timeout or retry ceiling.
    progress : ∀ token before → Σ Store.World (λ after → Σ Result (λ result → X.Completed (script token) before after result))
    progress token before with ownerProgress token ((reserve token , (unavailable mismatch , proj₂ (first (unavailable mismatch) token before))) ∷ [])
      (proj₂ (first (unavailable mismatch) token before)) (proj₁ (first (unavailable mismatch) token before))
    ... | after , result , X.completed events execution physical = after , result , X.completed
      ((reserve token , (unavailable mismatch , proj₂ (first (unavailable mismatch) token before))) ∷ events) (E.replied _ _ _ execution)
      (X.changed before _ _ _ ((refl , firstPhysical (unavailable mismatch) token before) , tt) physical)

    finishTranscript : ∀ token previous observation events result → E.Runs (finish token previous observation) events result →
      previous ++ events ≡ Result.transcript result
    finishTranscript token previous observation ._ ._ (E.replied _ _ (time , value) (E.returned _)) = refl

    inputTranscript : ∀ token previous snapshot input events result → E.Runs (afterInput token previous snapshot input) events result →
      previous ++ events ≡ Result.transcript result
    inputTranscript token previous snapshot (inj₁ fault) events result execution = finishTranscript _ _ _ _ _ execution
    inputTranscript token previous snapshot (inj₂ value) events result execution with configuration
    ... | nothing = finishTranscript _ _ _ _ _ execution
    ... | just cfg with settingsMatch cfg token snapshot
    ... | false = finishTranscript _ _ _ _ _ execution
    ... | true with Prepared.chunks value
    ... | [] = finishTranscript _ _ _ _ _ execution
    inputTranscript token previous snapshot (inj₂ value) ._ result (E.replied _ _ response {events} execution) | just cfg | true | _ ∷ _ =
      trans (sym (Lists.++-assoc previous ((embed token cfg (map Documents.Chunk.content (Prepared.chunks value)) , response) ∷ []) events))
        (finishTranscript _ _ _ _ _ execution)
    snapshotTranscript : ∀ token previous observation events result → E.Runs (afterSnapshot token previous observation) events result →
      previous ++ events ≡ Result.transcript result
    snapshotTranscript token previous (inj₁ fault) events result execution = finishTranscript _ _ _ _ _ execution
    snapshotTranscript token previous (inj₂ snapshot) events result execution
      with Store.lookupSaved snapshot token (publicationKey token) | Store.lookupSaved snapshot token Step.resultKey
    ... | nothing | nothing = inputTranscript token previous snapshot (storedPreparation token snapshot) events result execution
    ... | just _ | _ = finishTranscript _ _ _ _ _ execution
    ... | nothing | just _ = finishTranscript _ _ _ _ _ execution

    ownerTranscript : ∀ token previous value events result → E.Runs (afterOwner token previous value) events result →
      previous ++ events ≡ Result.transcript result
    ownerTranscript token previous (Step.done _) ._ result (E.replied _ _ observation {events} execution) =
      trans (sym (Lists.++-assoc previous ((readSources token , observation) ∷ []) events))
        (snapshotTranscript token (previous ++ ((readSources token , observation) ∷ [])) observation events result execution)
    ownerTranscript token previous (Step.needsInput _) .[] ._ (E.returned _) = Lists.++-identityʳ previous
    ownerTranscript token previous Step.needsRecovery .[] ._ (E.returned _) = Lists.++-identityʳ previous
    ownerTranscript token previous (Step.cancelled _) .[] ._ (E.returned _) = Lists.++-identityʳ previous

    -- The receipt records exactly this execution's events. Fresh preparation
    -- is tied by Atomic to its canonicalize/read trace and committing view;
    -- vectors come from this backend's embedding of the saved chunk texts.
    actualReceipts : ∀ token before after result (execution : X.Completed (script token) before after result) →
      X.Completed.events execution ≡ Result.transcript result
    actualReceipts token before after result (X.completed _ (E.replied _ _ observation execution) physical) =
      ownerTranscript token ((reserve token , observation) ∷ []) (proj₂ observation) _ result execution

    -- Assembly must retain this complete certificate, including observes;
    -- projecting a weaker durable-only operation would lose receipt binding.
    record Operation : Set₁ where
      field
        recovers : ∀ token initial interrupted after result → X.Interrupted (script token) initial interrupted →
          X.Completed (script token) interrupted after result → PublicGoal token initial after result
        progresses : ∀ token before → Σ Store.World (λ after → Σ Result (λ result → X.Completed (script token) before after result))
        observes : ∀ token before after result (execution : X.Completed (script token) before after result) →
          X.Completed.events execution ≡ Result.transcript result

    fullOperation : Operation
    fullOperation = record { recovers = converges; progresses = progress; observes = actualReceipts }

    toRecoverable : Operation → Recovery.RecoverableFor Store.World ℕ Result PublicGoal
    toRecoverable certificate = record
      { Effect = Effect; Reply = Reply; script = script; Atomic = Atomic
      ; converges = Operation.recovers certificate; progress = Operation.progresses certificate }

  CompletePublicationGoal = Goal

  -- The entry observes the actual journal before choosing a continuation.
  -- Fresh commits also retain the native transaction's next-step admission;
  -- neither fact is an argument that an MCP caller may supply.
  module Entry (coreConfiguration : Config.Config) (postgres : Controls.PostgreSQL) where
    module Body = Public coreConfiguration
    module Journal = Controls.Readback library postgres
    module Opaque = Controls.OpaqueJournal
    module Plan = Controls.Plan
    operationName : Text
    operationName = toList "load_document"

    record PrefixAdmission (token : ℕ) (before : Store.World) : Set where
      constructor prefixAdmission
      field
        context : Journal.ExecutionContext operationName token before
        actual : Journal.admission operationName token before ≡ Journal.admitted context
        declaredFirst declaredLast : Plan.Step
        selected : Opaque.next (Opaque.Complete.prefix (Journal.ExecutionContext.journal context)) ≡ just declaredFirst
        key : Plan.Step.id declaredFirst ≡ preparationKey token
        cursor : Opaque.Cursor token before (Plan.Saved.steps (Journal.ExecutionContext.plan context)) (declaredFirst ∷ declaredLast ∷ [])

    record FinalAdmission (token : ℕ) (before : Store.World) : Set where
      constructor finalAdmission
      field
        context : Journal.ExecutionContext operationName token before
        actual : Journal.admission operationName token before ≡ Journal.admitted context
        declaredLast : Plan.Step
        selected : Opaque.next (Opaque.Complete.prefix (Journal.ExecutionContext.journal context)) ≡ just declaredLast
        key : Plan.Step.id declaredLast ≡ publicationKey token
        cursor : Opaque.Cursor token before (Plan.Saved.steps (Journal.ExecutionContext.plan context)) (declaredLast ∷ [])

    data Outcome : Set where
      inspected : Journal.Result → Outcome
      executed : Body.Result → Outcome
    normalized : Outcome → Run.Value
    normalized (executed result) = Body.Result.value result
    normalized (inspected (Journal.completed _ value)) = Step.done value
    normalized (inspected (Journal.cancelled receipt _ _)) = Step.cancelled receipt
    normalized (inspected _) = Step.needsRecovery

    data Effect : Set where
      inspect : ℕ → Effect
      body : Body.Effect → Effect
    Reply : Effect → Set
    Reply (inspect _) = Store.World
    Reply (body effect) = Body.Reply effect
    module E = Effects.Protocol Effect Reply
    lift : Body.E.Script Body.Result → E.Script Outcome
    lift (Body.E.done result) = E.done (executed result)
    lift (Body.E.ask effect continuation) = E.ask (body effect) (λ reply → lift (continuation reply))
    branch : ℕ → Store.World → E.Script Outcome
    branch token snapshot with Journal.admission operationName token snapshot
    ... | Journal.returned result = E.done (inspected result)
    ... | Journal.admitted context = lift (Body.script token)
    script : ℕ → E.Script Outcome
    script token = E.ask (inspect token) (branch token)

    CommitAdmission : Store.World → (effect : Body.Effect) → Body.Reply effect → Set
    CommitAdmission before (Body.reserve token) (metadata , value) =
      FirstPublication metadata token before → PrefixAdmission token before
    CommitAdmission before (Body.publish token vectors) (time , value) =
      SecondPublication (publication vectors time) token before → FinalAdmission token before
    CommitAdmission before _ _ = ⊤
    Atomic : Store.World → (effect : Effect) → Reply effect → Store.World → Set
    Atomic before (inspect token) snapshot after = snapshot ≡ before × after ≡ before
    Atomic before (body effect) reply after = Body.Atomic before effect reply after × CommitAdmission before effect reply
    module X = Recovery.Execution Store.World Effect Reply Atomic

    -- A completed journal is read back before file/configuration/provider
    -- preparation. This is an actual one-read execution, with no store change.
    cachedReplay : ∀ token current binding raw →
      Journal.admission operationName token current ≡ Journal.returned (Journal.completed binding raw) →
      X.Completed (script token) current current (inspected (Journal.completed binding raw))
    cachedReplay token current binding raw known = X.completed
      ((inspect token , current) ∷ [])
      (E.replied _ _ current cachedBranchRun)
      (X.changed current _ _ current (refl , refl) (X.unchanged current))
      where
      cachedBranchRun : E.Runs (branch token current) [] (inspected (Journal.completed binding raw))
      cachedBranchRun rewrite known = E.returned _

    cachedReplayValue : ∀ token current binding raw →
      Journal.admission operationName token current ≡ Journal.returned (Journal.completed binding raw) →
      Σ Outcome (λ reply → X.Completed (script token) current current reply × normalized reply ≡ Step.done raw)
    cachedReplayValue token current binding raw known =
      inspected (Journal.completed binding raw) , cachedReplay token current binding raw known , refl

    -- Cached history and a malformed/foreign journal preserve the whole store.
    -- A running request instead owes the independent publication goal, even
    -- when a completed retry returns its original answer through readback.
    EntryGoal : ℕ → Store.World → Store.World → Outcome → Set
    EntryGoal token before after result =
      (after ≡ before × Σ Journal.Result (λ original →
        Journal.admission operationName token before ≡ Journal.returned original × result ≡ inspected original)) ⊎
      CompletePublicationGoal token before after (normalized result)

    eraseCompletion : ∀ program before after result events → E.Runs (lift program) events result →
      X.Changes before events after → Σ Body.Result (λ response → result ≡ executed response × Body.X.Completed program before after response)
    eraseCompletion (Body.E.done response) before .before ._ .[] (E.returned _) (X.unchanged _) =
      response , refl , Body.X.completed [] (Body.E.returned _) (Body.X.unchanged _)
    eraseCompletion (Body.E.ask effect next) before after result ._
      (E.replied .(body effect) _ reply execution) (X.changed _ _ _ middle physical changes)
      with eraseCompletion (next reply) middle after result _ execution changes
    ... | response , same , Body.X.completed events observedRun stores = response , same , Body.X.completed
      ((effect , reply) ∷ events) (Body.E.replied effect next reply observedRun) (Body.X.changed before effect reply middle (proj₁ physical) stores)

    record OriginalPrefix (program : Body.E.Script Body.Result) (before after : Store.World) (residual : E.Script Outcome) : Set where
      constructor originalPrefix
      field
        events : List Body.E.Event
        remaining : Body.E.Script Body.Result
        reached : Body.E.Prefix program events remaining
        physical : Body.X.Changes before events after
        projection : residual ≡ lift remaining

    erasePrefix : ∀ program before after residual events → E.Prefix (lift program) events residual →
      X.Changes before events after → OriginalPrefix program before after residual
    erasePrefix program before .before .(lift program) .[] (E.stopped _) (X.unchanged _) =
      originalPrefix [] program (Body.E.stopped _) (Body.X.unchanged _) refl
    erasePrefix (Body.E.ask effect next) before after residual ._
      (E.replied .(body effect) _ reply prefix) (X.changed _ _ _ middle physical changes)
      with erasePrefix (next reply) middle after residual _ prefix changes
    ... | originalPrefix events remaining reached stores same = originalPrefix
      ((effect , reply) ∷ events) remaining (Body.E.replied effect next reply reached)
      (Body.X.changed before effect reply middle (proj₁ physical) stores) same

    eraseActive : ∀ program before current after effect next reply events →
      E.Prefix (lift program) events (E.ask effect next) → X.Changes before events current →
      Atomic current effect reply after → Body.X.Interrupted program before after
    eraseActive program before current after effect next reply events prefix physical active
      with erasePrefix program before current (E.ask effect next) events prefix physical
    ... | originalPrefix sourceEvents (Body.E.done response) reached stores ()
    ... | originalPrefix sourceEvents (Body.E.ask sourceEffect sourceNext) reached stores refl =
      Body.X.beforeReply sourceEvents sourceEffect sourceNext current reply after reached stores (proj₁ active)

    donePrefixUnchanged : ∀ (result : Outcome) events residual before after → E.Prefix (E.done result) events residual →
      X.Changes before events after → after ≡ before
    donePrefixUnchanged result .[] .(E.done result) before .before (E.stopped _) (X.unchanged _) = refl

    doneCannotAsk : ∀ (result : Outcome) events effect next → E.Prefix (E.done result) events (E.ask effect next) → ⊥
    doneCannotAsk result events effect next ()

    CompletionMeaning : ℕ → Store.World → Store.World → Outcome → Set
    CompletionMeaning token before after (inspected result) =
      after ≡ before × Journal.admission operationName token before ≡ Journal.returned result
    CompletionMeaning token before after (executed result) =
      Σ (Journal.ExecutionContext operationName token before) (λ context →
        Journal.admission operationName token before ≡ Journal.admitted context ×
        Body.X.Completed (Body.script token) before after result)

    branchMeaning : ∀ token before after result events → E.Runs (branch token before) events result →
      X.Changes before events after → CompletionMeaning token before after result
    branchMeaning token before after result events execution physical
      with Journal.admission operationName token before in accepted
    ... | Journal.returned original with execution | physical
    ... | E.returned _ | X.unchanged _ = refl , accepted
    branchMeaning token before after result events execution physical | Journal.admitted context
      with eraseCompletion (Body.script token) before after result events execution physical
    ... | response , refl , sourceRun = context , accepted , sourceRun

    completionMeaning : ∀ token before after result → X.Completed (script token) before after result →
      CompletionMeaning token before after result
    completionMeaning token before after result
      (X.completed _ (E.replied _ _ .before execution) (X.changed _ _ _ .before (refl , refl) physical)) =
      branchMeaning token before after result _ execution physical

    completedMeetsGoal : ∀ token before after result → X.Completed (script token) before after result → EntryGoal token before after result
    completedMeetsGoal token before after (inspected result) complete
      with completionMeaning token before after (inspected result) complete
    ... | same , returned = inj₁ (same , result , returned , refl)
    completedMeetsGoal token before after (executed result) complete
      with completionMeaning token before after (executed result) complete
    ... | context , accepted , sourceRun = inj₂ (Body.converges token before before after result
      (Body.X.atPrefix [] (Body.script token) before (Body.E.stopped _) (Body.X.unchanged before)) sourceRun)

    InterruptionMeaning : ℕ → Store.World → Store.World → Set
    InterruptionMeaning token before interrupted = interrupted ≡ before ⊎
      Σ (Journal.ExecutionContext operationName token before) (λ context →
        Journal.admission operationName token before ≡ Journal.admitted context ×
        Body.X.Interrupted (Body.script token) before interrupted)

    interruptionMeaning : ∀ token before interrupted → X.Interrupted (script token) before interrupted →
      InterruptionMeaning token before interrupted
    interruptionMeaning token before .before
      (X.atPrefix .[] .(script token) .before (E.stopped _) (X.unchanged _)) = inj₁ refl
    interruptionMeaning token before interrupted
      (X.atPrefix _ residual .interrupted (E.replied _ _ .before {events} prefix)
        (X.changed _ _ _ .before (refl , refl) physical))
      with Journal.admission operationName token before in accepted
    ... | Journal.returned original = inj₁ (donePrefixUnchanged _ events residual before interrupted prefix physical)
    ... | Journal.admitted context with erasePrefix (Body.script token) before interrupted residual events prefix physical
    ... | originalPrefix sourceEvents remaining reached stores same = inj₂ (context , refl ,
      Body.X.atPrefix sourceEvents remaining interrupted reached stores)
    interruptionMeaning token before interrupted
      (X.beforeReply .[] .(inspect token) .(branch token) .before reply .interrupted
        (E.stopped _) (X.unchanged _) active) = inj₁ (proj₂ active)
    interruptionMeaning token before interrupted
      (X.beforeReply _ effect next current reply .interrupted (E.replied _ _ .before {events} prefix)
        (X.changed _ _ _ .before (refl , refl) physical) active)
      with Journal.admission operationName token before in accepted
    ... | Journal.returned original = Data.Empty.⊥-elim (doneCannotAsk _ events effect next prefix)
    ... | Journal.admitted context = inj₂ (context , refl ,
      eraseActive (Body.script token) before current interrupted effect next reply events prefix physical active)

    data JournalState (token : ℕ) (current : Store.World) : Set where
      pending : (context : Journal.ExecutionContext operationName token current) →
        Journal.admission operationName token current ≡ Journal.admitted context → JournalState token current
      completed : (binding : Store.BindingRow) (reply : Wire.Value) →
        Journal.admission operationName token current ≡ Journal.returned (Journal.completed binding reply) →
        (∀ initial received → Run.evaluate initial received token current ≡ (current , Step.done reply)) →
        JournalState token current

    finalPublicationKeepsJournal : ∀ token received before → SecondPublication received token before →
      FinalAdmission token before →
      JournalState token (proj₁ (second received token before))
    finalPublicationKeepsJournal token received before
      (saved , changed , reply , firstSaved , admitted , active , finalMissing , resultMissing , accepted)
      guard = subst (JournalState token) (sym (cong proj₁ fresh))
        (completed binding reply outcome (λ initial wanted →
          publishedEvaluation initial wanted received token before saved changed reply
            firstSaved admitted active finalMissing resultMissing accepted))
      where
      context = FinalAdmission.context guard
      binding = Journal.ExecutionContext.bindingRow context
      fresh = secondFresh received token before saved changed reply firstSaved admitted active finalMissing resultMissing accepted
      outcome : Journal.admission operationName token (Final.Kernel.publication (token , received) changed reply) ≡
        Journal.returned (Journal.completed binding reply)
      outcome = subst (λ key → Journal.admission operationName token
        (Store.saveAnswer (Store.saveAnswer changed token key reply) token Step.resultKey reply) ≡
        Journal.returned (Journal.completed binding reply)) (FinalAdmission.key guard)
        (Journal.finalPairCompletes operationName token before context (FinalAdmission.declaredLast guard) reply changed
          (FinalAdmission.selected guard) (FinalAdmission.cursor guard) resultMissing active
          (publicationJournal (token , received) before changed reply accepted))

    finishKeepsJournal : ∀ token vectors time value before after →
      Atomic before (body (Body.publish token vectors)) (time , value) after →
      JournalState token before → JournalState token after
    finishKeepsJournal token vectors time value before after (physical , admission) current
      with secondClassification (publication vectors time) token before
    ... | inj₁ same = subst (JournalState token) (sym (trans
      (cong proj₁ (Run.Second.atomicObservation (publication vectors time) token before after value physical)) same)) current
    ... | inj₂ fresh = subst (JournalState token)
      (sym (cong proj₁ (Run.Second.atomicObservation (publication vectors time) token before after value physical)))
      (finalPublicationKeepsJournal token (publication vectors time) before fresh (admission fresh))

    unavailableCannotPublish : ∀ token fault before changed reply →
      decidePreparation (token , unavailable fault) before ≡ inj₂ (changed , reply) → ⊥
    unavailableCannotPublish token fault before changed reply accepted with original token (Step.registration before)
    ... | inj₁ _ with accepted
    ... | ()
    unavailableCannotPublish token fault before changed reply () | inj₂ _

    faultCannotPublish : ∀ token fault time before changed reply →
      decidePublication (token , publication (inj₁ fault) time) before ≡ inj₂ (changed , reply) → ⊥
    faultCannotPublish token fault time before changed reply accepted with original token (Step.registration before)
    ... | inj₁ _ with accepted
    ... | ()
    faultCannotPublish token fault time before changed reply accepted | inj₂ actual with storedPreparation token before
    ... | inj₁ _ with accepted
    ... | ()
    faultCannotPublish token fault time before changed reply accepted | inj₂ actual | inj₂ value
      with sameProject (Request.project actual) (Prepared.project value) ∧
        hasOwner token value (Store.World.embeddingOwners before) ∧
        sameChunks (documentRows (Prepared.path value) before) (Prepared.previous value)
    ... | false with accepted
    ... | ()
    faultCannotPublish token fault time before changed reply () | inj₂ actual | inj₂ value | true

    unavailableAdmission : ∀ token fault before →
      FirstPublication (unavailable fault) token before → PrefixAdmission token before
    unavailableAdmission token fault before (changed , reply , _ , _ , _ , _ , _ , accepted) =
      Data.Empty.⊥-elim (unavailableCannotPublish token fault before changed reply accepted)
    faultAdmission : ∀ token fault time before →
      SecondPublication (publication (inj₁ fault) time) token before → FinalAdmission token before
    faultAdmission token fault time before (saved , changed , reply , _ , _ , _ , _ , _ , accepted) =
      Data.Empty.⊥-elim (faultCannotPublish token fault time before changed reply accepted)

    refusalProgress : ∀ token previous fault before → Σ Store.World (λ after → Σ Body.Result (λ result →
      X.Completed (lift (Body.finish token previous (inj₁ fault))) before after (executed result)))
    refusalProgress token previous fault before = proj₁ proposed , result , X.completed
      ((body (Body.publish token (inj₁ fault)) , (time , proj₂ proposed)) ∷ []) (E.replied _ _ _ (E.returned _))
      (X.changed before _ _ _ ((refl , secondPhysical received token before) , faultAdmission token fault time before) (X.unchanged _))
      where
      time = serverTime token before
      received = publication (inj₁ fault) time
      proposed = second received token before
      result = Body.completed (proj₂ proposed) (previous ++ ((Body.publish token (inj₁ fault) , (time , proj₂ proposed)) ∷ []))

    ownerProgress : ∀ token previous value before → Σ Store.World (λ after → Σ Body.Result (λ result →
      X.Completed (lift (Body.afterOwner token previous value)) before after (executed result)))
    ownerProgress token previous (Step.done _) before with refusalProgress token
      (previous ++ ((Body.readSources token , inj₁ mismatch) ∷ [])) mismatch before
    ... | after , result , X.completed events execution physical = after , result , X.completed
      ((body (Body.readSources token) , inj₁ mismatch) ∷ events) (E.replied _ _ _ execution)
      (X.changed before _ _ before (refl , tt) physical)
    ownerProgress token previous (Step.needsInput diagnostic) before = before , Body.completed (Step.needsInput diagnostic) previous ,
      X.completed [] (E.returned _) (X.unchanged _)
    ownerProgress token previous Step.needsRecovery before = before , Body.completed Step.needsRecovery previous ,
      X.completed [] (E.returned _) (X.unchanged _)
    ownerProgress token previous (Step.cancelled receipt) before = before , Body.completed (Step.cancelled receipt) previous ,
      X.completed [] (E.returned _) (X.unchanged _)

    bodyProgress : ∀ token before → Σ Store.World (λ after → Σ Body.Result (λ result →
      X.Completed (lift (Body.script token)) before after (executed result)))
    bodyProgress token before with ownerProgress token
      ((Body.reserve token , (unavailable mismatch , proj₂ (first (unavailable mismatch) token before))) ∷ [])
      (proj₂ (first (unavailable mismatch) token before)) (proj₁ (first (unavailable mismatch) token before))
    ... | after , result , X.completed events execution physical = after , result , X.completed
      ((body (Body.reserve token) , (unavailable mismatch , proj₂ (first (unavailable mismatch) token before))) ∷ events)
      (E.replied _ _ _ execution)
      (X.changed before _ _ _ (((refl , firstPhysical (unavailable mismatch) token before) , tt) , unavailableAdmission token mismatch before) physical)

    branchProgress : ∀ token before → Σ Store.World (λ after → Σ Outcome (λ result →
      X.Completed (branch token before) before after result))
    branchProgress token before with Journal.admission operationName token before
    ... | Journal.returned result = before , inspected result , X.completed [] (E.returned _) (X.unchanged _)
    ... | Journal.admitted context with bodyProgress token before
    ... | after , result , complete = after , executed result , complete

    progress : ∀ token before → Σ Store.World (λ after → Σ Outcome (λ result → X.Completed (script token) before after result))
    progress token before with branchProgress token before
    ... | after , result , X.completed events execution physical = after , result , X.completed
      ((inspect token , before) ∷ events) (E.replied _ _ before execution)
      (X.changed before _ _ before (refl , refl) physical)

    Observed : ℕ → Store.World → Store.World → Outcome → Set
    Observed token before after (inspected result) = CompletionMeaning token before after (inspected result)
    Observed token before after (executed result) =
      Σ (Journal.ExecutionContext operationName token before) (λ context →
        Journal.admission operationName token before ≡ Journal.admitted context ×
        Σ (Body.X.Completed (Body.script token) before after result) (λ execution →
          Body.X.Completed.events execution ≡ Body.Result.transcript result))

    actualReceipts : Body.Operation → ∀ token before after result → X.Completed (script token) before after result →
      Observed token before after result
    actualReceipts certificate token before after (inspected result) execution =
      completionMeaning token before after (inspected result) execution
    actualReceipts certificate token before after (executed result) execution
      with completionMeaning token before after (executed result) execution
    ... | context , admitted , sourceRun = context , admitted , sourceRun ,
      Body.Operation.observes certificate token before after result sourceRun

    returnedSame : ∀ token before firstResult secondResult →
      Journal.returned {operation = operationName} {token = token} {before = before} firstResult ≡ Journal.returned secondResult →
      firstResult ≡ secondResult
    returnedSame token before firstResult .firstResult refl = refl
    admittedCannotReturn : ∀ token before context result →
      Journal.admitted {operation = operationName} {token = token} {before = before} context ≡ Journal.returned result → ⊥
    admittedCannotReturn token before context result ()

    cachedOriginalGoal : ∀ token before current result → Body.X.Interrupted (Body.script token) before current →
      JournalState token current → Journal.admission operationName token current ≡ Journal.returned result →
      CompletePublicationGoal token before current (normalized (inspected result))
    cachedOriginalGoal token before current result cut (pending context accepted) returned =
      Data.Empty.⊥-elim (admittedCannotReturn token current context result (trans (sym accepted) returned))
    cachedOriginalGoal token before current result cut (completed binding reply accepted evaluates) returned
      with returnedSame token current (Journal.completed binding reply) result (trans (sym accepted) returned)
    ... | refl with Body.interruptedInvariant token before current cut (unavailable mismatch)
      (publication (inj₁ mismatch) (serverTime token current))
    ... | originalFirst , originalFinal , retained = subst
      (λ pair → CompletePublicationGoal token before (proj₁ pair) (proj₂ pair))
      (sym (trans (sym (evaluates (unavailable mismatch) (publication (inj₁ mismatch) (serverTime token current)))) retained))
      (meaning originalFirst originalFinal token before)

    prefixPublicationKeepsJournal : ∀ token metadata before → FirstPublication metadata token before →
      PrefixAdmission token before → JournalState token (proj₁ (first metadata token before))
    prefixPublicationKeepsJournal token metadata before
      (changed , reply , admitted , active , firstMissing , finalMissing , resultMissing , accepted) guard
      with Journal.preserveAfterNext operationName token before (PrefixAdmission.context guard)
        (PrefixAdmission.declaredFirst guard) (PrefixAdmission.declaredLast guard) [] reply changed
        (PrefixAdmission.selected guard) (PrefixAdmission.cursor guard) active
        (preparationJournal (token , metadata) before changed reply accepted)
    ... | context , current = subst (JournalState token) (sym (cong proj₁ fresh))
      (subst (JournalState token) (cong (λ key → Store.saveAnswer changed token key reply) (PrefixAdmission.key guard))
        (pending context current))
      where
      fresh = freshFirst metadata token before changed reply admitted active firstMissing finalMissing resultMissing accepted

    reserveKeepsJournal : ∀ token metadata value before after →
      Atomic before (body (Body.reserve token)) (metadata , value) after →
      JournalState token before → JournalState token after
    reserveKeepsJournal token metadata value before after ((physical , source) , admission) current
      with firstClassification metadata token before
    ... | inj₁ same = subst (JournalState token) (sym (trans
      (cong proj₁ (Run.First.atomicObservation metadata token before after value physical)) same)) current
    ... | inj₂ fresh = subst (JournalState token)
      (sym (cong proj₁ (Run.First.atomicObservation metadata token before after value physical)))
      (prefixPublicationKeepsJournal token metadata before fresh (admission fresh))

    bodyKeepsJournal : ∀ token effect reply before after → Body.Owned token effect →
      Atomic before (body effect) reply after → JournalState token before → JournalState token after
    bodyKeepsJournal token .(Body.reserve token) (metadata , value) before after Body.ownerOwned physical current =
      reserveKeepsJournal token metadata value before after physical current
    bodyKeepsJournal token .(Body.readSources token) (inj₁ fault) before .before Body.sourcesOwned (refl , tt) current = current
    bodyKeepsJournal token .(Body.readSources token) (inj₂ .before) before .before Body.sourcesOwned ((refl , refl) , tt) current = current
    bodyKeepsJournal token .(Body.embed token cfg content) reply before .before (Body.embedOwned cfg content) (refl , tt) current = current
    bodyKeepsJournal token .(Body.publish token vectors) (time , value) before after (Body.publishOwned vectors) physical current =
      finishKeepsJournal token vectors time value before after physical current

    prefixKeepsJournal : ∀ token program events residual before after → Body.Scoped token program →
      E.Prefix (lift program) events residual → X.Changes before events after →
      JournalState token before → JournalState token after
    prefixKeepsJournal token program .[] .(lift program) before .before scoped (E.stopped _) (X.unchanged _) current = current
    prefixKeepsJournal token .(Body.E.ask effect continuation) ._ residual before after
      (Body.asked effect continuation own later) (E.replied .(body effect) _ reply prefix)
      (X.changed _ _ _ middle physical rest) current =
      prefixKeepsJournal token (continuation reply) _ residual middle after (later reply) prefix rest
        (bodyKeepsJournal token effect reply before middle own physical current)

    activeKeepsJournal : ∀ token program events effect next reply before current after → Body.Scoped token program →
      E.Prefix (lift program) events (E.ask effect next) → X.Changes before events current → Atomic current effect reply after →
      JournalState token before → JournalState token after
    activeKeepsJournal token program events effect next reply before current after scoped prefix physical active initial
      with erasePrefix program before current (E.ask effect next) events prefix physical
    ... | originalPrefix sourceEvents (Body.E.done response) reached stores ()
    ... | originalPrefix sourceEvents (Body.E.ask sourceEffect sourceNext) reached stores refl =
      bodyKeepsJournal token sourceEffect reply current after
        (Body.activeOwned token sourceEffect sourceNext (proj₂ (Body.prefixScoped token program sourceEvents _ scoped reached)))
        active (prefixKeepsJournal token program events _ before current scoped prefix physical initial)

    interruptedHasJournal : ∀ token before interrupted context →
      Journal.admission operationName token before ≡ Journal.admitted context →
      X.Interrupted (script token) before interrupted → JournalState token interrupted
    interruptedHasJournal token before .before context accepted
      (X.atPrefix .[] .(script token) .before (E.stopped _) (X.unchanged _)) = pending context accepted
    interruptedHasJournal token before interrupted context accepted
      (X.atPrefix _ residual .interrupted (E.replied _ _ .before {events} prefix)
        (X.changed _ _ _ .before (refl , refl) physical))
      with Journal.admission operationName token before in observedAdmission
    ... | Journal.returned original = Data.Empty.⊥-elim
      (admittedCannotReturn token before context original (sym accepted))
    ... | Journal.admitted actual = prefixKeepsJournal token (Body.script token) events residual before interrupted
      (Body.scriptScoped token) prefix physical (pending actual observedAdmission)
    interruptedHasJournal token before interrupted context accepted
      (X.beforeReply .[] .(inspect token) .(branch token) .before reply .interrupted
        (E.stopped _) (X.unchanged _) active) = subst (JournalState token) (sym (proj₂ active)) (pending context accepted)
    interruptedHasJournal token before interrupted context accepted
      (X.beforeReply _ effect next current reply .interrupted (E.replied _ _ .before {events} prefix)
        (X.changed _ _ _ .before (refl , refl) physical) active)
      with Journal.admission operationName token before in observedAdmission
    ... | Journal.returned original = Data.Empty.⊥-elim (doneCannotAsk _ events effect next prefix)
    ... | Journal.admitted actual = activeKeepsJournal token (Body.script token) events effect next reply before current interrupted
      (Body.scriptScoped token) prefix physical active (pending actual observedAdmission)

    -- The actual entry may publish an owner and saved answers, then replace
    -- document data. None of those commits changes the original operation
    -- registration or its cancellation row, including a lost reply boundary.
    MetadataFrame : ℕ → Store.World → Store.World → Set
    MetadataFrame token before current = Step.registration current ≡ Step.registration before ×
      Store.lookupCancellation current token ≡ Store.lookupCancellation before token

    private
      unchangedMetadata : ∀ token before current → current ≡ before → MetadataFrame token before current
      unchangedMetadata token before current same = cong Step.registration same ,
        cong (λ world → Store.lookupCancellation world token) same

      followedMetadata : ∀ token before middle current → MetadataFrame token before middle →
        MetadataFrame token middle current → MetadataFrame token before current
      followedMetadata token before middle current earlier later =
        trans (proj₁ later) (proj₁ earlier) , trans (proj₂ later) (proj₂ earlier)

      firstMetadata : ∀ metadata token before → MetadataFrame token before (proj₁ (first metadata token before))
      firstMetadata metadata token before with firstClassification metadata token before
      ... | inj₁ same = unchangedMetadata token before _ same
      ... | inj₂ (changed , reply , admitted , active , firstMissing , lastMissing , resultMissing , accepted) =
        subst (MetadataFrame token before)
          (sym (cong proj₁ (freshFirst metadata token before changed reply admitted active firstMissing lastMissing resultMissing accepted)))
          (Prefix.keepsRegistration (token , metadata) before changed reply accepted ,
           Prefix.keepsCancellation (token , metadata) before changed reply accepted)

      secondMetadata : ∀ received token before → MetadataFrame token before (proj₁ (second received token before))
      secondMetadata received token before with Store.lookupSaved before token (preparationKey token)
      ... | nothing = refl , refl
      ... | just _ = Final.registrationUnchanged (token , received) before ,
        Final.cancellationUnchanged token (token , received) before

      bodyAtomicMetadata : ∀ token before current effect reply → Body.Owned token effect →
        Body.Atomic before effect reply current → MetadataFrame token before current
      bodyAtomicMetadata token before current .(Body.reserve token) (metadata , reply) Body.ownerOwned physical =
        subst (MetadataFrame token before)
          (sym (cong proj₁ (Run.First.atomicObservation metadata token before current reply (proj₁ physical))))
          (firstMetadata metadata token before)
      bodyAtomicMetadata token before current .(Body.readSources token) (inj₁ fault) Body.sourcesOwned same =
        unchangedMetadata token before current same
      bodyAtomicMetadata token before current .(Body.readSources token) (inj₂ snapshot) Body.sourcesOwned (snapshotSame , same) =
        unchangedMetadata token before current same
      bodyAtomicMetadata token before current .(Body.embed token cfg content) reply (Body.embedOwned cfg content) same =
        unchangedMetadata token before current same
      bodyAtomicMetadata token before current .(Body.publish token vectors) (time , reply) (Body.publishOwned vectors) physical =
        subst (MetadataFrame token before)
          (sym (cong proj₁ (Run.Second.atomicObservation (publication vectors time) token before current reply physical)))
          (secondMetadata (publication vectors time) token before)

      bodyChangesMetadata : ∀ token initial before events current →
        All (λ event → Body.Owned token (proj₁ event)) events →
        Body.X.Changes before events current → MetadataFrame token initial before → MetadataFrame token initial current
      bodyChangesMetadata token initial before [] .before [] (Body.X.unchanged _) old = old
      bodyChangesMetadata token initial before ((effect , reply) ∷ events) current (own ∷ owners)
        (Body.X.changed _ _ _ middle physical rest) old =
        bodyChangesMetadata token initial middle events current owners rest
          (followedMetadata token initial before middle old (bodyAtomicMetadata token before middle effect reply own physical))

      bodyInterruptedMetadata : ∀ token before current → Body.X.Interrupted (Body.script token) before current →
        MetadataFrame token before current
      bodyInterruptedMetadata token before current (Body.X.atPrefix events residual .current prefix physical) =
        bodyChangesMetadata token before before events current
          (proj₁ (Body.prefixScoped token (Body.script token) events residual (Body.scriptScoped token) prefix))
          physical (refl , refl)
      bodyInterruptedMetadata token before current
        (Body.X.beforeReply events effect continuation middle reply .current prefix physical active)
        with Body.prefixScoped token (Body.script token) events (Body.E.ask effect continuation) (Body.scriptScoped token) prefix
      ... | owners , residual = followedMetadata token before middle current
        (bodyChangesMetadata token before before events middle owners physical (refl , refl))
        (bodyAtomicMetadata token middle current effect reply (Body.activeOwned token effect continuation residual) active)

    interruptedMetadataFrame : ∀ token before current → X.Interrupted (script token) before current →
      Step.registration current ≡ Step.registration before ×
      Store.lookupCancellation current token ≡ Store.lookupCancellation before token
    interruptedMetadataFrame token before current cut with interruptionMeaning token before current cut
    ... | inj₁ same = unchangedMetadata token before current same
    ... | inj₂ (context , admitted , bodyCut) = bodyInterruptedMetadata token before current bodyCut

    converges : ∀ token before interrupted after result → X.Interrupted (script token) before interrupted →
      X.Completed (script token) interrupted after result → EntryGoal token before after result
    converges token before interrupted after result cut retry with interruptionMeaning token before interrupted cut
    ... | inj₁ same = subst (λ start → EntryGoal token start after result) same
      (completedMeetsGoal token interrupted after result retry)
    ... | inj₂ (context , accepted , sourceCut) with result | completionMeaning token interrupted after result retry
    ... | inspected original | same , actualReadback = inj₂ (subst
      (λ final → CompletePublicationGoal token before final (normalized (inspected original))) (sym same)
      (cachedOriginalGoal token before interrupted original sourceCut
        (interruptedHasJournal token before interrupted context accepted cut) actualReadback))
    ... | executed response | actualContext , admitted , sourceRun =
      inj₂ (Body.converges token before interrupted after response sourceCut sourceRun)

    -- This is the entry-level certificate consumed by public assembly. It
    -- retains the actual inspection and source/provider transcript proof;
    -- the private two-phase kernel cannot bypass the journal guard.
    record Operation : Set₁ where
      field
        recovers : ∀ token before interrupted after result → X.Interrupted (script token) before interrupted →
          X.Completed (script token) interrupted after result → EntryGoal token before after result
        progresses : ∀ token before → Σ Store.World (λ after → Σ Outcome (λ result → X.Completed (script token) before after result))
        observes : ∀ token before after result → X.Completed (script token) before after result → Observed token before after result
    fullOperation : Operation
    fullOperation = record
      { recovers = converges; progresses = progress; observes = actualReceipts Body.fullOperation }
    toRecoverable : Operation → Recovery.RecoverableFor Store.World ℕ Outcome EntryGoal
    toRecoverable certificate = record
      { Effect = Effect; Reply = Reply; script = script; Atomic = Atomic
      ; converges = Operation.recovers certificate; progress = Operation.progresses certificate }
