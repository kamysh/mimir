{-# OPTIONS --safe #-}
-- Independent publication owes every required component and the resulting
-- posterior. Provider observations are receipts, never caller assertions.
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
  module G = Ground.Business databaseSum calculator
  module N = Inference.NumericalOutcome databaseSum

  data Diagnostic : Set where
    requestFault : Validation.Fault → Diagnostic
    preparation : Embedding.Correction.Claim → Diagnostic
    numerical : G.Diagnostic → Diagnostic

  Outcome = Diagnostic ⊎ (Store.World × Wire.Value)

  revalidation : Diagnostic
  revalidation = preparation (Embedding.preparationDecision Embedding.Correction.arguments
    (Validation.key "content" ∷ [])
    (toList "Publication no longer has its original owner, complete vector and unchanged indexed support. Read the original operation outcome and the supporting document before deciding how to proceed. No belief was stored."))

  updated : ℤ → P.State → Graph.BeliefValues → Graph.BeliefValues
  updated publicationTime changes belief with P.lookup (Graph.BeliefValues.identity belief) changes
  ... | nothing = belief
  ... | just counts = Evidence.accounted publicationTime (Evidence.updated belief counts)

  module Selected (publicationTime : ℤ) (belief : Graph.BeliefValues) (selected : N.Context) where
    open N.Context selected
    module A = P.Assess seed external edges targets

    Goal : Store.World → Outcome → Set
    Goal before (inj₁ (numerical diagnostic)) = G.Selected.DiagnosticGoal publicationTime selected diagnostic
    Goal before (inj₁ _) = ⊥
    Goal before (inj₂ (after , reply)) = Σ P.State (λ counts →
      P.ValidState counts ×
      map proj₁ counts ≡ map P.Node.identity (N.ordered selected) ×
      P.PosteriorGoal seed external edges (N.ordered selected) counts ×
      after ≡ N.proposed publicationTime selected before counts ×
      reply ≡ Encode.belief (updated publicationTime (N.writes selected counts) belief))

    report = calculator seed external edges targets

    checked : ∀ before → Σ Outcome (Goal before)
    checked before with A.check report in assessed
    ... | A.rejected = inj₁ (numerical (G.rejectedReport report)) , assessed
    ... | A.repeated final visited seen incomplete runs =
      inj₁ (numerical (G.repeated final visited)) , seen , incomplete , runs
    ... | A.accepted counts valid shape complete =
      inj₂ (N.proposed publicationTime selected before counts ,
        Encode.belief (updated publicationTime (N.writes selected counts) belief)) ,
      counts , valid , shape , complete , refl , refl

    keepsJournal : ∀ before after reply → Goal before (inj₂ (after , reply)) →
      Store.World.operations after ≡ Store.World.operations before
    keepsJournal before after reply (counts , valid , shape , complete , framed , answered) =
      G.Selected.publicationKeepsJournal publicationTime selected before after Ground.answer
        (Numeric.project (N.writes selected counts) ,
          (edges , Perm.↭-refl , counts , valid , shape , complete , framed , refl) , refl)

  -- Pairing is a complete desired store change: the exact belief/provenance,
  -- its complete vector, all validated support, and consumption of its owner.
  paired : ℤ → Graph.BeliefValues → Origin.Provenance → Embedding.Prepared → Store.World → Store.World
  paired publicationTime belief origin value = Embedding.Atomic.paired 0 calculator publicationTime belief (just origin) value

  Goal : ℤ → Graph.BeliefValues → Origin.Provenance → Embedding.Prepared → Store.World → Outcome → Set
  Goal publicationTime belief origin value before outcome
    with Ranking.lookup (Graph.BeliefValues.identity belief) (Store.beliefs before)
  ... | just _ = outcome ≡ inj₁ revalidation
  ... | nothing with Embedding.ownsPreparation belief (Store.World.embeddingOwners before) ∧
    Embedding.usableVector (Embedding.Prepared.vector value) ∧
    Embedding.allSupportCurrent belief before (Embedding.supports value)
  ... | false = outcome ≡ inj₁ revalidation
  ... | true with N.prepare (N.recompute (Graph.BeliefValues.identity belief ∷ []))
    (paired publicationTime belief origin value before)
  ... | inj₁ issue = outcome ≡ inj₁ (numerical (G.preparation issue))
  ... | inj₂ selected = Selected.Goal publicationTime belief selected
    (paired publicationTime belief origin value before) outcome

  checked : ∀ publicationTime belief origin value before →
    Σ Outcome (Goal publicationTime belief origin value before)
  checked publicationTime belief origin value before
    with Ranking.lookup (Graph.BeliefValues.identity belief) (Store.beliefs before)
  ... | just _ = inj₁ revalidation , refl
  ... | nothing with Embedding.ownsPreparation belief (Store.World.embeddingOwners before) ∧
    Embedding.usableVector (Embedding.Prepared.vector value) ∧
    Embedding.allSupportCurrent belief before (Embedding.supports value)
  ... | false = inj₁ revalidation , refl
  ... | true with N.prepare (N.recompute (Graph.BeliefValues.identity belief ∷ []))
    (paired publicationTime belief origin value before)
  ... | inj₁ issue = inj₁ (numerical (G.preparation issue)) , refl
  ... | inj₂ selected = Selected.checked publicationTime belief selected
    (paired publicationTime belief origin value before)

  journalUnchanged : ∀ publicationTime belief origin value before after reply →
    proj₁ (checked publicationTime belief origin value before) ≡ inj₂ (after , reply) →
    Store.World.operations after ≡ Store.World.operations before
  journalUnchanged publicationTime belief origin value before after reply accepted
    with Ranking.lookup (Graph.BeliefValues.identity belief) (Store.beliefs before)
  ... | just _ with accepted
  ... | ()
  journalUnchanged publicationTime belief origin value before after reply accepted | nothing
    with Embedding.ownsPreparation belief (Store.World.embeddingOwners before) ∧
      Embedding.usableVector (Embedding.Prepared.vector value) ∧
      Embedding.allSupportCurrent belief before (Embedding.supports value)
  ... | false with accepted
  ... | ()
  journalUnchanged publicationTime belief origin value before after reply accepted | nothing | true
    with N.prepare (N.recompute (Graph.BeliefValues.identity belief ∷ []))
      (paired publicationTime belief origin value before)
  ... | inj₁ issue with accepted
  ... | ()
  journalUnchanged publicationTime belief origin value before after reply accepted | nothing | true | inj₂ selected =
    Selected.keepsJournal publicationTime belief selected (paired publicationTime belief origin value before) after reply
      (subst (Selected.Goal publicationTime belief selected (paired publicationTime belief origin value before))
        accepted (proj₂ (Selected.checked publicationTime belief selected (paired publicationTime belief origin value before))))

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

-- The allocator parameter is the actual successful PostgreSQL allocation
-- receipt. It is never a field of the agent request or an expected result.
module OwnerPhase (format : Encoding.Formatting) (conversion : Conversion.Contract)
  (databaseSum : List Float → Float) (calculator : P.Calculator)
  (allocation : ℕ → Request → Allocation) where
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

  decode : Wire.Value → Validation.Fault ⊎ Request
  decode raw with D.readTool Tools.insertBelief raw
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ (Public.mutation (Mutation.belief content probability confidence project memory (just origin))) =
    inj₂ (request content probability confidence project memory origin)
  ... | inj₂ _ = inj₁ mismatch

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

  decide : ℕ → Store.World → B.Outcome
  decide token before with original token (Step.registration before)
  ... | inj₁ fault = inj₁ (B.requestFault fault)
  ... | inj₂ requested = inj₂
    (O.intended token requested (allocation token requested) before , O.answer (allocation token requested))

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
    after ≡ Saved.Base.firstPublication token (O.intended token requested (allocation token requested) before)
      (O.answer (allocation token requested)) ×
    reply ≡ Step.done (O.answer (allocation token requested))

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

  module Atomic = Step.AtomicStep ℕ B.Diagnostic Saved.execute Saved.stable Saved.expectedPhysical
  module Certified = Atomic.Certified Goal meaning
  ownerPhase = Certified.operation

-- A retry may obtain another actual packet before publication. Once one
-- packet was committed, every later preparation choice is irrelevant: the
-- complete stored world and original answer are retained before preparation.
module PacketReplay (Input Diagnostic : Set)
  (token : Input → ℕ) (key : Input → Text)
  (distinct : ∀ input → key input ≡ Step.resultKey → ⊥)
  (admit : Input → Step.Registration → Maybe Diagnostic)
  (firstAttempt laterAttempt : Input → Store.World → Diagnostic ⊎ (Store.World × Wire.Value))
  (firstJournal : ∀ input before after reply → firstAttempt input before ≡ inj₂ (after , reply) →
    Store.World.operations after ≡ Store.World.operations before)
  (laterJournal : ∀ input before after reply → laterAttempt input before ≡ inj₂ (after , reply) →
    Store.World.operations after ≡ Store.World.operations before) where

  module First = Step.Admitted Input Diagnostic token key distinct firstAttempt firstJournal admit
  module Later = Step.Admitted Input Diagnostic token key distinct laterAttempt laterJournal admit

  knownReplay : ∀ input before saved final →
    admit input (Step.registration before) ≡ nothing →
    Store.lookupCancellation before (token input) ≡ nothing →
    Store.lookupSaved before (token input) (key input) ≡ just saved →
    Store.lookupSaved before (token input) Step.resultKey ≡ just final →
    Later.execute input before ≡ (before , Step.done saved)
  knownReplay input before saved final admitted active step result
    rewrite admitted | active | step | result = refl

  publishedPacketIsFixed : ∀ input before after reply →
    admit input (Step.registration before) ≡ nothing →
    Store.lookupCancellation before (token input) ≡ nothing →
    Store.lookupSaved before (token input) (key input) ≡ nothing →
    Store.lookupSaved before (token input) Step.resultKey ≡ nothing →
    firstAttempt input before ≡ inj₂ (after , reply) →
    Later.execute input (First.Kernel.publication input after reply) ≡
      (First.Kernel.publication input after reply , Step.done reply)
  publishedPacketIsFixed input before after reply admitted active step result accepted =
    knownReplay input (First.Kernel.publication input after reply) reply reply
      (trans (cong (admit input) (First.Kernel.publicationKeepsRegistration input before after reply accepted)) admitted)
      (trans (First.Kernel.publicationKeepsCancellation input before after reply accepted) active)
      (First.Kernel.publishedStepReadable input before after reply accepted step)
      (First.Kernel.publishedResultReadable input before after reply accepted result)
