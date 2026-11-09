{-# OPTIONS --safe #-}
-- Independent publication requires its embedding and explicit source record.
-- Source references do not alter probabilities. Provider observations are
-- receipts, never caller assertions.
module Mimir.IndependentBeliefRecovery where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.Empty using (⊥)
open import Data.Float.Base using (Float)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; subst)
open import Relation.Nullary using (does)
open import Mimir.Text using (Text)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Mimir.ApplicationStore as Store
import Mimir.BeliefEmbedding as Embedding
import Mimir.CandidateGraph as Graph
import Mimir.ConfigurationValues as Config
import Mimir.EvidenceValidity as Evidence
import Mimir.GraphRecords as Records
import Mimir.GraphNumerics as Numeric
import Mimir.GroundingRecovery as Ground
import Mimir.IndependentProvenance as Origin
import Mimir.InferenceStorageBinding as Inference
import Mimir.LearningCandidates as Memory
import Mimir.PosteriorComputation as P
import Mimir.ProjectDeletion as Project
import Mimir.PublicEncoding as Encoding
import Mimir.PublicRequest as Public
import Mimir.GraphMutationProtocol as Mutation
import Mimir.RecoverableStoreSequence as Sequence
import Mimir.RecoverableStoreStep as Step
import Mimir.RegisteredStoreAdmission as Admission
import Mimir.StandardLibrary as Conversion
import Mimir.RetrievalRanking as Ranking
import Mimir.StructuredValue as Wire
import Mimir.Validation as Validation
import Mimir.ToolCatalog as Tools

record Request : Set where
  constructor request
  field
    content : Text
    probability confidence : Float
    project : Maybe Text
    memory : Memory.Memory
    provenance : Origin.Provenance
    grounding : List Embedding.Citation

-- This value is returned by PostgreSQL allocation/readback. It is not an
-- identifier or timestamp selected by an MCP caller.
record Allocation : Set where
  constructor allocated
  field identity : ℕ; createdAt : ℤ

initial : Request → Allocation → Maybe Graph.BeliefValues
initial requested allocation = Records.newBelief (Allocation.identity allocation)
  (Allocation.createdAt allocation) (Request.content requested)
  (Request.probability requested) (Request.confidence requested)
  (Request.project requested) (Request.memory requested)

-- Bind actual provider choices, excluding credentials and execution-only
-- cache/batch settings. Local ignores its configured model field today.
embeddingIdentity : Maybe Config.Embeddings → Wire.Value
embeddingIdentity nothing = Wire.null
embeddingIdentity (just configured) with Config.Embeddings.backend configured
... | Config.local = Encoding.object
  (("backend" , Wire.string (toList "local")) ∷
   ("model" , Wire.string (toList "BAAI/bge-base-en-v1.5")) ∷ [])
... | Config.voyage = Encoding.object
  (("backend" , Wire.string (toList "voyage")) ∷
   ("model" , Wire.string (Config.Embeddings.model configured)) ∷
   ("input_type" , Wire.string (toList "document")) ∷
   ("truncation" , Wire.boolean false) ∷ [])
... | Config.openai = Encoding.object
  (("backend" , Wire.string (toList "openai")) ∷
   ("model" , Wire.string (Config.Embeddings.model configured)) ∷ [])

operationSettings : Maybe Config.Embeddings → Wire.Value
operationSettings configured = Encoding.object (("embeddings" , embeddingIdentity configured) ∷ [])

module Owner (format : Encoding.Formatting) where
  module Encode = Encoding.Encode format

  row : ℕ → Request → Allocation → Store.EmbeddingOwnerRow
  row token requested allocation = Store.embeddingOwnerRow
    (Allocation.identity allocation) (Request.project requested)
    (Allocation.createdAt allocation) (just token)

  intended : ℕ → Request → Allocation → Store.World → Store.World
  intended token requested allocation before = record before
    { embeddingOwners = row token requested allocation ∷ Store.World.embeddingOwners before }

  answer : Allocation → Wire.Value
  answer allocation = Encoding.object
    (("id" , Encode.uuid (Allocation.identity allocation)) ∷
     ("created_at" , Encode.timestamp (Allocation.createdAt allocation)) ∷ [])

  keepsJournal : ∀ token requested allocation before →
    Store.World.operations (intended token requested allocation before) ≡ Store.World.operations before
  keepsJournal token requested allocation before = refl

module Business (format : Encoding.Formatting)
  (databaseSum : List Float → Float) (calculator : P.Calculator) where
  module Encode = Encoding.Encode format

  data Diagnostic : Set where
    requestFault : Validation.Fault → Diagnostic
    preparation : Embedding.Correction.Claim → Diagnostic

  Outcome = Diagnostic ⊎ (Store.World × Wire.Value)

  revalidation : Diagnostic
  revalidation = preparation (Embedding.preparationDecision Embedding.Correction.arguments
    (Validation.key "grounding" ∷ [])
    (toList "Publication requires the original owner, complete embedding and unchanged explicitly cited indexed passages. Read the original outcome and sources, then open the user dialog before changing the request. No belief was stored."))

  paired : ℤ → Graph.BeliefValues → Maybe Origin.Provenance → Embedding.Prepared → Store.World → Store.World
  paired publicationTime = Embedding.Atomic.paired 0 calculator publicationTime

  complete : Graph.BeliefValues → Embedding.Prepared → Store.World → Bool
  complete belief value before with Ranking.lookup (Graph.BeliefValues.identity belief) (Store.beliefs before)
  ... | just _ = false
  ... | nothing = Embedding.preparationCurrent belief (Embedding.supports value) before ∧
    Embedding.usableVector (Embedding.Prepared.vector value)

  -- Native readback derives its displayed probability/confidence from the
  -- unchanged stored counts. This reuses existing application arithmetic;
  -- no approximation, comparison threshold or formatter is introduced.
  readback : Graph.BeliefValues → Graph.BeliefValues
  readback = Embedding.readback

  -- This goal fixes the complete business state and original public result.
  -- A source reference adds no GROUNDS weight and recomputes no posterior.
  Goal : ℤ → Graph.BeliefValues → Maybe Origin.Provenance → Embedding.Prepared → Store.World → Outcome → Set
  Goal publicationTime belief origin value before (inj₁ diagnostic) =
    complete belief value before ≡ false × diagnostic ≡ revalidation
  Goal publicationTime belief origin value before (inj₂ (after , reply)) =
    complete belief value before ≡ true ×
    after ≡ paired publicationTime belief origin value before × reply ≡ Encode.belief (readback belief)

  checked : ∀ publicationTime belief origin value before →
    Σ Outcome (Goal publicationTime belief origin value before)
  checked publicationTime belief origin value before with complete belief value before in accepted
  ... | false = inj₁ revalidation , accepted , refl
  ... | true = inj₂ (paired publicationTime belief origin value before , Encode.belief (readback belief)) , accepted , refl , refl

  journalUnchanged : ∀ publicationTime belief origin value before after reply →
    proj₁ (checked publicationTime belief origin value before) ≡ inj₂ (after , reply) →
    Store.World.operations after ≡ Store.World.operations before
  journalUnchanged publicationTime belief origin value before after reply accepted
    with subst (Goal publicationTime belief origin value before) accepted
      (proj₂ (checked publicationTime belief origin value before))
  ... | valid , refl , sameReply = frame publicationTime belief origin value before
    where
    frame : ∀ publicationTime belief origin value before →
      Store.World.operations (paired publicationTime belief origin value before) ≡ Store.World.operations before
    frame publicationTime belief nothing value before = refl
    frame publicationTime belief (just origin) value before = refl

  weightedEvidenceIsUnchanged : ∀ publicationTime belief origin value before →
    Store.World.grounds (paired publicationTime belief origin value before) ≡ Store.World.grounds before
  weightedEvidenceIsUnchanged publicationTime belief nothing value before = refl
  weightedEvidenceIsUnchanged publicationTime belief (just origin) value before = refl

ownerKey publicationKey : ℕ → Text
ownerKey _ = toList "[\"store.reserve_belief_preparation\",null]"
publicationKey _ = toList "[\"store.publish_prepared_belief\",null]"

ownerDistinct : ∀ token → ownerKey token ≡ Step.resultKey → ⊥
ownerDistinct token ()
phasesDifferent : ∀ token → ownerKey token ≡ publicationKey token → ⊥
phasesDifferent token ()

module ProviderSettings where
  open Project.Registered using (fields; fieldText; fieldNull; fieldFalse)
  isString : Maybe Wire.Value → Bool
  isString (just (Wire.string _)) = true
  isString _ = false

  local : Wire.Value → Bool
  local = fields (toList "backend" ∷ toList "model" ∷ []) λ view →
    fieldText (toList "local") (view (toList "backend")) ∧
    fieldText (toList "BAAI/bge-base-en-v1.5") (view (toList "model"))

  voyage : Wire.Value → Bool
  voyage = fields (toList "backend" ∷ toList "model" ∷ toList "input_type" ∷ toList "truncation" ∷ []) λ view →
    fieldText (toList "voyage") (view (toList "backend")) ∧ isString (view (toList "model")) ∧
    fieldText (toList "document") (view (toList "input_type")) ∧ fieldFalse (view (toList "truncation"))

  openai : Wire.Value → Bool
  openai = fields (toList "backend" ∷ toList "model" ∷ []) λ view →
    fieldText (toList "openai") (view (toList "backend")) ∧ isString (view (toList "model"))

  provider : Maybe Wire.Value → Bool
  provider nothing = false
  provider (just Wire.null) = true
  provider (just value) = local value ∨ voyage value ∨ openai value

  admitted : Wire.Value → Bool
  admitted = fields (toList "embeddings" ∷ []) λ view → provider (view (toList "embeddings"))

module Binding (format : Encoding.Formatting) (conversion : Conversion.Contract)
  (databaseSum : List Float → Float) (calculator : P.Calculator) where
  module O = Owner format
  module B = Business format databaseSum calculator
  module D = Public.Decode conversion

  descriptor : Admission.PairDescriptor
  descriptor = Admission.pairDescriptor (toList "insert_belief")
    (toList "store.reserve_belief_preparation") (ownerKey 0)
    (toList "store.publish_prepared_belief") (publicationKey 0)

  mismatch : Validation.Fault
  mismatch = Validation.fault (Validation.key "operation_token" ∷ []) Validation.wrongIdentity
    "Read the original belief request and its server-selected embedding settings. Retain the original token and plan; do not invent a provider, identity or replacement request."

  decodePublic : Wire.Value → Validation.Fault ⊎ Request
  decodePublic raw with D.readBoundTool Tools.insertBelief raw
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ (Public.mutation (Mutation.belief content probability confidence project memory (just origin) cited)) =
    inj₂ (request content probability confidence project memory origin cited)
  ... | inj₂ _ = inj₁ mismatch

  -- Stored declarations can predate the citation field. Decoding their
  -- absent field as [] preserves completed replay, while new publication's
  -- preparation still refuses empty citations. Public admission remains
  -- strict and requires the field; no stored declaration is rewritten.
  decode : Wire.Value → Validation.Fault ⊎ Request
  decode raw@(Wire.object fields) with Wire.Object.normalize fields (toList "grounding")
  ... | nothing = decodePublic (Wire.object ((toList "grounding" , Wire.array []) ∷ fields))
  ... | just _ = decodePublic raw
  decode raw = decodePublic raw

  original : ℕ → Step.Registration → Validation.Fault ⊎ Request
  original token registration with Admission.resolvePair descriptor token registration
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ (reserved , binding) with ProviderSettings.admitted (Store.BindingRow.settings binding)
  ... | false = inj₁ mismatch
  ... | true = decode (Store.BindingRow.arguments binding)

  admit : ℕ → Step.Registration → Maybe B.Diagnostic
  admit token registration with original token registration
  ... | inj₁ fault = just (B.requestFault fault)
  ... | inj₂ _ = nothing

-- Allocation is the metadata in this particular PostgreSQL reply. Admission
-- is independent of that observation and cannot select a new identity.
module OwnerPhase (format : Encoding.Formatting) (conversion : Conversion.Contract)
  (databaseSum : List Float → Float) (calculator : P.Calculator)
  (allocation : Allocation) where
  open Binding format conversion databaseSum calculator public

  decide : ℕ → Store.World → B.Outcome
  decide token before with original token (Step.registration before)
  ... | inj₁ fault = inj₁ (B.requestFault fault)
  ... | inj₂ requested = inj₂
    (O.intended token requested allocation before , O.answer allocation)

  decidesBound : ∀ token before requested → original token (Step.registration before) ≡ inj₂ requested →
    decide token before ≡ inj₂ (O.intended token requested allocation before , O.answer allocation)
  decidesBound token before requested bound rewrite bound = refl

  keepsJournal : ∀ token before changed reply → decide token before ≡ inj₂ (changed , reply) →
    Store.World.operations changed ≡ Store.World.operations before
  keepsJournal token before changed reply accepted with original token (Step.registration before)
  ... | inj₁ fault with accepted
  ... | ()
  keepsJournal token before changed reply accepted | inj₂ requested with accepted
  ... | refl = refl

  module Saved = Sequence.SavedPrefix ℕ B.Diagnostic (λ token → token)
    ownerKey publicationKey ownerDistinct phasesDifferent decide keepsJournal admit

  FreshGoal : ℕ → Store.World → Store.World → Saved.Reply → Set
  FreshGoal token before after reply with original token (Step.registration before)
  ... | inj₁ fault = after ≡ before × reply ≡ Step.needsInput (B.requestFault fault)
  ... | inj₂ requested =
    after ≡ Saved.Base.firstPublication token (O.intended token requested allocation before)
      (O.answer allocation) ×
    reply ≡ Step.done (O.answer allocation)

  freshMeaning : ∀ token before → FreshGoal token before
    (proj₁ (Saved.fresh token before)) (proj₂ (Saved.fresh token before))
  freshMeaning token before with original token (Step.registration before)
  ... | inj₁ fault = refl , refl
  ... | inj₂ requested = refl , refl

  Goal : ℕ → Store.World → Store.World → Saved.Reply → Set
  Goal token before after reply with admit token (Step.registration before)
  ... | just diagnostic = after ≡ before × reply ≡ Step.needsInput diagnostic
  ... | nothing with Store.lookupCancellation before token
  ... | just cancelled = after ≡ before × reply ≡ Step.cancelled cancelled
  ... | nothing with Store.lookupSaved before token (ownerKey token)
    | Store.lookupSaved before token (publicationKey token) | Store.lookupSaved before token Step.resultKey
  ... | just saved | nothing | nothing = after ≡ before × reply ≡ Step.done saved
  ... | just saved | just _ | just _ = after ≡ before × reply ≡ Step.done saved
  ... | just _ | nothing | just _ = after ≡ before × reply ≡ Step.needsRecovery
  ... | just _ | just _ | nothing = after ≡ before × reply ≡ Step.needsRecovery
  ... | nothing | nothing | just _ = after ≡ before × reply ≡ Step.needsRecovery
  ... | nothing | just _ | nothing = after ≡ before × reply ≡ Step.needsRecovery
  ... | nothing | just _ | just _ = after ≡ before × reply ≡ Step.needsRecovery
  ... | nothing | nothing | nothing = FreshGoal token before after reply

  meaning : ∀ token before → Goal token before
    (proj₁ (Saved.execute token before)) (proj₂ (Saved.execute token before))
  meaning token before with admit token (Step.registration before)
  ... | just diagnostic = refl , refl
  ... | nothing with Store.lookupCancellation before token
  ... | just cancelled = refl , refl
  ... | nothing with Store.lookupSaved before token (ownerKey token)
    | Store.lookupSaved before token (publicationKey token) | Store.lookupSaved before token Step.resultKey
  ... | just _ | nothing | nothing = refl , refl
  ... | just _ | just _ | just _ = refl , refl
  ... | just _ | nothing | just _ = refl , refl
  ... | just _ | just _ | nothing = refl , refl
  ... | nothing | nothing | just _ = refl , refl
  ... | nothing | just _ | nothing = refl , refl
  ... | nothing | just _ | just _ = refl , refl
  ... | nothing | nothing | nothing = freshMeaning token before
