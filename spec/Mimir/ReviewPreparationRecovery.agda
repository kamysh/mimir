{-# OPTIONS --safe #-}
-- Review preparation publishes only PostgreSQL owners and their original
-- answers. Beliefs, vectors, citations and the review remain unchanged.
module Mimir.ReviewPreparationRecovery where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer using (ℤ) renaming (_≟_ to _≟ℤ_)
open import Data.Float.Base using (Float)
open import Data.List using (List; []; _∷_; map; length; _++_; filterᵇ)
open import Data.List.Relation.Unary.All using (All; []; _∷_; all?)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; ¬_; yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; sym; trans; subst)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.ApplicationStore as Store
import Mimir.DatabaseTransaction as DB
import Mimir.ExperienceRead as Read
import Mimir.ExperienceSchema as Experience
import Mimir.LearningInput as Input
import Mimir.LearningCandidates as Candidates
import Mimir.LearningStore as Learning
import Mimir.OperationControls as Controls
import Mimir.PosteriorComputation as Posterior
import Mimir.ProjectDeletion as Project
import Mimir.PublicEncoding as Encoding
import Mimir.RecoverableStoreStep as Step
import Mimir.RegisteredStoreAdmission as Admission
import Mimir.Recovery as Recovery
import Mimir.ReviewObservation as Observation
import Mimir.ReviewPublicationRecovery as Review
import Mimir.StandardLibrary as Library
import Mimir.StructuredValue as Wire
import Mimir.Validation as Validation
import Data.List.Properties as Lists
import Data.Fin as Fin

alongObservation : ∀ {A B : Set} (original : A) (branch : (actual : A) → original ≡ actual → B)
  actual observed → branch original refl ≡ branch actual observed
alongObservation original branch .original refl = refl

differentSummands : ∀ {A B : Set} {first : A} {second : B} → inj₂ second ≡ inj₁ first → ⊥
differentSummands ()

record Allocation : Set where
  constructor allocation
  field identity : ℕ; createdAt : ℤ; project : Text

owner : ℕ → Allocation → Store.EmbeddingOwnerRow
owner token value = Store.embeddingOwnerRow (Allocation.identity value)
  (just (Allocation.project value)) (Allocation.createdAt value) (just token)

module AllocationEncoding (format : Encoding.Formatting) where
  module Encode = Encoding.Encode format
  answer : Allocation → Wire.Value
  answer value = Encoding.object
    (("id" , Encode.uuid (Allocation.identity value)) ∷
     ("created_at" , Encode.timestamp (Allocation.createdAt value)) ∷
     ("project" , Wire.string (Allocation.project value)) ∷ [])

  -- This is the actual saved-answer Serde observation. It is not a theorem
  -- about formatting every natural number or parsing a caller's expected ID.
  data AllocationRead (raw : Wire.Value) : Set where
    decoded : (value : Allocation) → answer value ≡ raw → AllocationRead raw
    malformed : Validation.Fault → AllocationRead raw

  record Codec : Set where
    field readAllocation : (raw : Wire.Value) → AllocationRead raw

  module Saved (codec : Codec) where
    read : Wire.Value → Validation.Fault ⊎ Allocation
    read raw with Codec.readAllocation codec raw
    ... | decoded value represented = inj₂ value
    ... | malformed fault = inj₁ fault

    represented : ∀ raw value → read raw ≡ inj₂ value → answer value ≡ raw
    represented raw value accepted with Codec.readAllocation codec raw
    ... | decoded actual encoded with accepted
    ... | refl = encoded
    represented raw value () | malformed fault

-- No business component is projected away: this comparison removes only the
-- two metadata tables that this prefix is allowed to extend.
protected : Store.World → Store.World
protected before = record before
  { embeddingOwners = []
  ; operations = record (Store.World.operations before) { savedReplies = [] } }

publication : ℕ → Text → Allocation → Wire.Value → Store.World → Store.World
publication token step value raw before = Store.saveAnswer
  (record before { embeddingOwners = owner token value ∷ Store.World.embeddingOwners before }) token step raw

ownerPublication = publication

publicationKeepsProtected : ∀ token step value raw before →
  protected (publication token step value raw before) ≡ protected before
publicationKeepsProtected token step value raw before
  with Store.lookupSaved before token step
... | just _ = refl
... | nothing = refl

publicationKeepsRegistration : ∀ token step value raw before →
  Step.registration (publication token step value raw before) ≡ Step.registration before
publicationKeepsRegistration token step value raw before =
  Store.savingAnswerPreservesOperationInputs
    (record before { embeddingOwners = owner token value ∷ Store.World.embeddingOwners before }) token step raw

publicationKeepsCancellation : ∀ token step value raw before queried →
  Store.lookupCancellation (publication token step value raw before) queried ≡ Store.lookupCancellation before queried
publicationKeepsCancellation token step value raw before queried =
  Store.savingAnswerPreservesCancellation
    (record before { embeddingOwners = owner token value ∷ Store.World.embeddingOwners before }) token step raw queried

publicationKeepsOldAnswer : ∀ token step value raw before queried key original →
  Store.lookupSaved before queried key ≡ just original →
  Store.lookupSaved (publication token step value raw before) queried key ≡ just original
publicationKeepsOldAnswer token step value raw before queried key original old
  with Store.replyKey? queried key (Store.savedReplyRow token step raw)
... | no different = trans (Store.otherSavedAnswerPreserved
  (record before { embeddingOwners = owner token value ∷ Store.World.embeddingOwners before }) token step raw queried key different) old
... | yes (refl , refl) rewrite old = old

publicationReadable : ∀ token step value raw before → Store.lookupSaved before token step ≡ nothing →
  Store.lookupSaved (publication token step value raw before) token step ≡ just raw
publicationReadable token step value raw before absent rewrite absent = Store.headReplyReadable token step raw _

publicationOwners : ∀ token step value raw before → Store.World.embeddingOwners
  (publication token step value raw before) ≡ owner token value ∷ Store.World.embeddingOwners before
publicationOwners token step value raw before with Store.lookupSaved before token step
... | just _ = refl
... | nothing = refl

missingSource malformedJournal changedSettings : Validation.Fault
missingSource = Validation.fault (Validation.key "review" ∷ Validation.key "experience_revision" ∷ [])
  Validation.staleRevision
  "The original experience revision is no longer current. Read the experience and saved review, then open the user dialog. No review or belief was published."
malformedJournal = Validation.fault (Validation.key "operation_token" ∷ []) Validation.wrongIdentity
  "The saved answers are not a complete prefix of the original review plan. Read the original plan and answers and open the user dialog; do not skip an owner, invent an allocation or repeat a confirmed review."
changedSettings = Validation.fault (Validation.key "settings" ∷ []) Validation.wrongIdentity
  "The current embedding model differs from this unfinished review's original model. Read its original binding and open the user dialog. Do not switch models, replace the token or invent preparation identities."

open Controls using (Addressing; empty; more; addressing?)

-- Check the complete journal, not just the next requested answer. A saved
-- answer after an absent earlier step is a gap; an extra/duplicate row is
-- rejected by the separate exact row count. No row is dropped or repaired.
module Journal (format : Encoding.Formatting) (codec : AllocationEncoding.Codec format) where
  module Saved = AllocationEncoding.Saved format codec
  module Shared = Controls.PrefixJournal Allocation Saved.read
  open Shared public hiding (extendComplete)

  -- The handler's owner row and answer are one physical transaction. The
  -- shared prefix law applies after the metadata-only owner insertion.
  extendComplete : ∀ token before steps (journal : Complete token before steps) first value raw →
    Addressing steps → next (Complete.prefix journal) ≡ just first → Saved.read raw ≡ inj₂ value →
    Complete token (ownerPublication token (Controls.Plan.Step.id first) value raw before) steps
  extendComplete token before steps journal first value raw addresses selected decoded
    with Shared.relocateComplete token before
      (record before { embeddingOwners = owner token value ∷ Store.World.embeddingOwners before }) steps refl journal
  ... | relocated , unchanged = Shared.extendComplete token
    (record before { embeddingOwners = owner token value ∷ Store.World.embeddingOwners before }) steps relocated first value raw
    addresses (trans unchanged selected) decoded

-- Actual source lookup is repeated under the writer lock at each fresh owner
-- insertion. Its project is read from that same current source row.
sourceProject : Review.Request → Store.World → Validation.Fault ⊎ Text
sourceProject requested before with Read.get (Input.Review.experienceID (Review.Request.original requested))
  (Learning.World.current (Store.World.learning before))
... | nothing = inj₁ missingSource
... | just current with Input.Review.experienceRevision (Review.Request.original requested) ≟ℤ Observation.Snapshot.revision current
... | no _ = inj₁ missingSource
... | yes _ = inj₂ (Experience.Experience.project (Observation.Snapshot.experience current))

module Registered (library : Library.Contract) (format : Encoding.Formatting)
  (database : ℕ) (databaseSum : List Float → Float)
  (calculator : Posterior.Calculator) (dependencies : Review.Dependencies)
  (codec : AllocationEncoding.Codec format) (postgres : Controls.PostgreSQL) where
  module Final = Review.FinalBody library format database databaseSum calculator dependencies
  module Plan = Controls.Plan
  module Enc = AllocationEncoding format
  module Saved = Enc.Saved codec
  module J = Journal format codec
  module Readback = Controls.Readback library postgres

  keys : List Candidates.Candidate → List Text
  keys [] = []
  keys (Candidates.patternCandidate _ _ _ ∷ rest) = keys rest
  keys (Candidates.belief candidateKey _ _ _ ∷ rest) = candidateKey ∷ keys rest

  declared : Text → Plan.Step
  declared candidateKey = Plan.canonicalStep library (toList "store.reserve_belief_preparation") (just candidateKey)

  ownerStepsAsKeys : ∀ candidates → Final.ownerSteps candidates ≡ map declared (keys candidates)
  ownerStepsAsKeys [] = refl
  ownerStepsAsKeys (Candidates.patternCandidate _ _ _ ∷ rest) = ownerStepsAsKeys rest
  ownerStepsAsKeys (Candidates.belief candidateKey _ _ _ ∷ rest) = cong (declared candidateKey ∷_) (ownerStepsAsKeys rest)

  record Context : Set where
    constructor context
    field token : ℕ
          request : Review.Request
          allocations : List (Text × Store.EmbeddingOwnerRow)

  data Result : Set where
    ready : Context → Result
    stopped : Step.Result Validation.Fault → Result

  data Decision : Set where
    stop : Step.Result Validation.Fault → Decision
    run : Review.Request → Decision

  afterSettings : Wire.Value → Store.BindingRow → Review.Request → Decision
  afterSettings current binding requested with Lists.≡-dec Fin._≟_
    (Library.Contract.compactJSON library current)
    (Library.Contract.compactJSON library (Store.BindingRow.settings binding))
  ... | yes _ = run requested
  ... | no _ = stop (Step.needsInput changedSettings)

  beforePreparation : Wire.Value → ℕ → Store.BindingRow → Store.World → Decision
  beforePreparation current token binding before with Final.original token (Step.registration before)
  ... | inj₁ fault = stop (Step.needsInput fault)
  ... | inj₂ (requested , _) with J.check token before (Final.ownerSteps (Input.Review.candidates (Review.Request.original requested)))
  ... | inj₁ fault = stop (Step.needsInput fault)
  ... | inj₂ _ with addressing? (Final.ownerSteps (Input.Review.candidates (Review.Request.original requested)))
  ... | no _ = stop (Step.needsInput malformedJournal)
  ... | yes _ with Review.PreparationStatus.inspect requested before
  ... | Review.PreparationStatus.blocked fault = stop (Step.needsInput fault)
  ... | Review.PreparationStatus.alreadyApplied _ = run requested
  ... | Review.PreparationStatus.waiting _ _ = afterSettings current binding requested

  inspect : Wire.Value → ℕ → Store.World → Decision
  inspect current token before with Readback.admission (toList "review_experience") token before
  ... | Readback.admitted loaded = beforePreparation current token (Readback.ExecutionContext.bindingRow loaded) before
  ... | Readback.returned (Readback.completed _ reply) = stop (Step.done reply)
  ... | Readback.returned (Readback.cancelled cancellation _ _) = stop (Step.cancelled cancellation)
  ... | Readback.returned (Readback.pending _ _ _) = stop Step.needsRecovery
  ... | Readback.returned (Readback.inconsistent _ _) = stop (Step.needsInput malformedJournal)
  ... | Readback.returned (Readback.needsRecovery _) = stop Step.needsRecovery
  ... | Readback.returned Readback.unknownToken = stop (Step.needsInput malformedJournal)
  ... | Readback.returned Readback.reserved = stop (Step.needsInput malformedJournal)
  ... | Readback.returned (Readback.awaitingPlan _) = stop (Step.needsInput malformedJournal)
  ... | Readback.returned (Readback.awaitingCompletion _) = stop Step.needsRecovery

  record Admitted (token : ℕ) (before : Store.World) (requested : Review.Request) : Set where
    constructor admitted
    field time : ℤ
          original : Final.original token (Step.registration before) ≡ inj₂ (requested , time)
          journal : J.Complete token before (Final.ownerSteps (Input.Review.candidates (Review.Request.original requested)))
          addresses : Addressing (Final.ownerSteps (Input.Review.candidates (Review.Request.original requested)))

  settingsRequest : ∀ current binding original requested → afterSettings current binding original ≡ run requested → original ≡ requested
  settingsRequest current binding original requested accepted with Lists.≡-dec Fin._≟_
    (Library.Contract.compactJSON library current)
    (Library.Contract.compactJSON library (Store.BindingRow.settings binding))
  ... | yes _ with accepted
  ... | refl = refl
  settingsRequest current binding original requested () | no _

  preparationAdmitted : ∀ current token binding before requested → beforePreparation current token binding before ≡ run requested →
    Admitted token before requested
  preparationAdmitted current token binding before requested accepted
    with Final.original token (Step.registration before) in original
  ... | inj₁ _ with accepted
  ... | ()
  preparationAdmitted current token binding before requested accepted | inj₂ (actual , time)
    with J.check token before (Final.ownerSteps (Input.Review.candidates (Review.Request.original actual)))
  ... | inj₁ _ with accepted
  ... | ()
  preparationAdmitted current token binding before requested accepted | inj₂ (actual , time) | inj₂ journal
    with addressing? (Final.ownerSteps (Input.Review.candidates (Review.Request.original actual)))
  ... | no _ with accepted
  ... | ()
  preparationAdmitted current token binding before requested accepted | inj₂ (actual , time) | inj₂ journal | yes addresses
    with Review.PreparationStatus.inspect actual before
  ... | Review.PreparationStatus.blocked _ with accepted
  ... | ()
  preparationAdmitted current token binding before requested accepted | inj₂ (actual , time) | inj₂ journal | yes addresses
    | Review.PreparationStatus.alreadyApplied _ with accepted
  ... | refl = admitted time original journal addresses
  preparationAdmitted current token binding before requested accepted | inj₂ (actual , time) | inj₂ journal | yes addresses
    | Review.PreparationStatus.waiting _ _ with settingsRequest current binding actual requested accepted
  ... | refl = admitted time original journal addresses

  inspectAdmitted : ∀ current token before requested → inspect current token before ≡ run requested → Admitted token before requested
  inspectAdmitted current token before requested accepted with Readback.admission (toList "review_experience") token before
  ... | Readback.admitted loaded = preparationAdmitted current token (Readback.ExecutionContext.bindingRow loaded) before requested accepted
  inspectAdmitted current token before requested () | Readback.returned (Readback.completed _ _)
  inspectAdmitted current token before requested () | Readback.returned (Readback.cancelled _ _ _)
  inspectAdmitted current token before requested () | Readback.returned (Readback.inconsistent _ _)
  inspectAdmitted current token before requested () | Readback.returned (Readback.needsRecovery _)
  inspectAdmitted current token before requested () | Readback.returned (Readback.pending _ _ _)
  inspectAdmitted current token before requested () | Readback.returned Readback.unknownToken
  inspectAdmitted current token before requested () | Readback.returned Readback.reserved
  inspectAdmitted current token before requested () | Readback.returned (Readback.awaitingPlan _)
  inspectAdmitted current token before requested () | Readback.returned (Readback.awaitingCompletion _)

  record AllocationReceipt : Set where
    constructor allocatedRow
    field value : Allocation
          decoded : Saved.read (Enc.answer value) ≡ inj₂ value

  data AllocationObservation : Set where
    allocated : AllocationReceipt → AllocationObservation
    unavailable : Validation.Fault → AllocationObservation

  wrongProject : Validation.Fault
  wrongProject = Validation.fault (Validation.key "preparation_owner" ∷ Validation.key "project" ∷ [])
    Validation.wrongIdentity
    "The returned preparation owner does not belong to the original experience's current project. Read the owner, original binding and experience, then open the user dialog. No review or belief was published."

  fresh : AllocationObservation → ℕ → Text → Review.Request → Store.World → Store.World × Step.Result Validation.Fault
  fresh observed token candidateKey requested before with sourceProject requested before
  ... | inj₁ fault = before , Step.needsInput fault
  ... | inj₂ project with observed
  ... | unavailable fault = before , Step.needsInput fault
  ... | allocated receipt with Allocation.project (AllocationReceipt.value receipt) ≟Text project
  ... | no _ = before , Step.needsInput wrongProject
  ... | yes _ = publication token (Plan.Step.id (declared candidateKey)) (AllocationReceipt.value receipt)
    (Enc.answer (AllocationReceipt.value receipt)) before , Step.done (Enc.answer (AllocationReceipt.value receipt))

  admittedOwner : AllocationObservation → (token : ℕ) → Text → (requested : Review.Request) → (before : Store.World) →
    J.Complete token before (Final.ownerSteps (Input.Review.candidates (Review.Request.original requested))) →
    Store.World × Step.Result Validation.Fault
  admittedOwner observed token candidateKey requested before journal with Store.lookupSaved before token (Plan.Step.id (declared candidateKey))
  ... | just raw = before , Step.done raw
  ... | nothing with J.next (J.Complete.prefix journal)
  ... | nothing = before , Step.needsInput malformedJournal
  ... | just next with Plan.Step.id next ≟Text Plan.Step.id (declared candidateKey)
  ... | no _ = before , Step.needsInput malformedJournal
  ... | yes _ = fresh observed token candidateKey requested before

  execute : AllocationObservation → ℕ → Text → Store.World → Store.World × Step.Result Validation.Fault
  execute observed token candidateKey before with Final.original token (Step.registration before)
  ... | inj₁ fault = before , Step.needsInput fault
  ... | inj₂ (requested , _) with Store.lookupCancellation before token
  ... | just cancellation = before , Step.cancelled cancellation
  ... | nothing with J.check token before (Final.ownerSteps (Input.Review.candidates (Review.Request.original requested)))
  ... | inj₁ fault = before , Step.needsInput fault
  ... | inj₂ journal with addressing? (Final.ownerSteps (Input.Review.candidates (Review.Request.original requested)))
  ... | no _ = before , Step.needsInput malformedJournal
  ... | yes _ = admittedOwner observed token candidateKey requested before journal

  data Change (token : ℕ) (before : Store.World) : Store.World → Set where
    stayed : Change token before before
    added : ∀ requested time →
      Final.original token (Step.registration before) ≡ inj₂ (requested , time) →
      (journal : J.Complete token before (Final.ownerSteps (Input.Review.candidates (Review.Request.original requested)))) →
      Addressing (Final.ownerSteps (Input.Review.candidates (Review.Request.original requested))) →
      (next : Plan.Step) → J.next (J.Complete.prefix journal) ≡ just next →
      (receipt : AllocationReceipt) →
      sourceProject requested before ≡ inj₂ (Allocation.project (AllocationReceipt.value receipt)) →
      Change token before (publication token (Plan.Step.id next) (AllocationReceipt.value receipt)
        (Enc.answer (AllocationReceipt.value receipt)) before)

  freshChange : ∀ observed token candidateKey requested time before →
    Final.original token (Step.registration before) ≡ inj₂ (requested , time) →
    (journal : J.Complete token before (Final.ownerSteps (Input.Review.candidates (Review.Request.original requested)))) →
    Addressing (Final.ownerSteps (Input.Review.candidates (Review.Request.original requested))) →
    (next : Plan.Step) → J.next (J.Complete.prefix journal) ≡ just next →
    Plan.Step.id next ≡ Plan.Step.id (declared candidateKey) →
    Change token before (proj₁ (fresh observed token candidateKey requested before))
  freshChange observed token candidateKey requested time before original journal addresses next selected same
    with sourceProject requested before in source
  ... | inj₁ _ = stayed
  ... | inj₂ project with observed
  ... | unavailable _ = stayed
  ... | allocated receipt with Allocation.project (AllocationReceipt.value receipt) ≟Text project
  ... | no _ = stayed
  ... | yes sameProject = subst (Change token before)
      (cong (λ key → publication token key (AllocationReceipt.value receipt) (Enc.answer (AllocationReceipt.value receipt)) before) same)
      (added requested time original journal addresses next selected receipt
        (trans source (cong inj₂ (sym sameProject))))

  admittedChange : ∀ observed token candidateKey requested time before →
    Final.original token (Step.registration before) ≡ inj₂ (requested , time) →
    (journal : J.Complete token before (Final.ownerSteps (Input.Review.candidates (Review.Request.original requested)))) →
    Addressing (Final.ownerSteps (Input.Review.candidates (Review.Request.original requested))) →
    Change token before (proj₁ (admittedOwner observed token candidateKey requested before journal))
  admittedChange observed token candidateKey requested time before original journal addresses
    with Store.lookupSaved before token (Plan.Step.id (declared candidateKey))
  ... | just _ = stayed
  ... | nothing with J.next (J.Complete.prefix journal) in selected
  ... | nothing = stayed
  ... | just next with Plan.Step.id next ≟Text Plan.Step.id (declared candidateKey)
  ... | no _ = stayed
  ... | yes same = freshChange observed token candidateKey requested time before original journal addresses next selected same

  executeChange : ∀ observed token candidateKey before →
    Change token before (proj₁ (execute observed token candidateKey before))
  executeChange observed token candidateKey before with Final.original token (Step.registration before) in original
  ... | inj₁ _ = stayed
  ... | inj₂ (requested , time) with Store.lookupCancellation before token
  ... | just _ = stayed
  ... | nothing with J.check token before (Final.ownerSteps (Input.Review.candidates (Review.Request.original requested)))
  ... | inj₁ _ = stayed
  ... | inj₂ journal with addressing? (Final.ownerSteps (Input.Review.candidates (Review.Request.original requested)))
  ... | no _ = stayed
  ... | yes addresses = admittedChange observed token candidateKey requested time before original journal addresses

  freshDone : ∀ observed token candidateKey requested before raw →
    Store.lookupSaved before token (Plan.Step.id (declared candidateKey)) ≡ nothing →
    proj₂ (fresh observed token candidateKey requested before) ≡ Step.done raw →
    Store.lookupSaved (proj₁ (fresh observed token candidateKey requested before)) token (Plan.Step.id (declared candidateKey)) ≡ just raw
  freshDone observed token candidateKey requested before raw absent confirmed with sourceProject requested before
  ... | inj₁ _ with confirmed
  ... | ()
  freshDone observed token candidateKey requested before raw absent confirmed | inj₂ project with observed
  ... | unavailable _ with confirmed
  ... | ()
  freshDone observed token candidateKey requested before raw absent confirmed | inj₂ project | allocated receipt
    with Allocation.project (AllocationReceipt.value receipt) ≟Text project
  ... | no _ with confirmed
  ... | ()
  freshDone observed token candidateKey requested before raw absent confirmed | inj₂ project | allocated receipt | yes _
    with confirmed
  ... | refl = publicationReadable token (Plan.Step.id (declared candidateKey)) (AllocationReceipt.value receipt)
    (Enc.answer (AllocationReceipt.value receipt)) before absent

  admittedDone : ∀ observed token candidateKey requested before journal raw →
    proj₂ (admittedOwner observed token candidateKey requested before journal) ≡ Step.done raw →
    Store.lookupSaved (proj₁ (admittedOwner observed token candidateKey requested before journal)) token (Plan.Step.id (declared candidateKey)) ≡ just raw
  admittedDone observed token candidateKey requested before journal raw confirmed
    with Store.lookupSaved before token (Plan.Step.id (declared candidateKey)) in saved
  ... | just original with confirmed
  ... | refl = saved
  admittedDone observed token candidateKey requested before journal raw confirmed | nothing
    with J.next (J.Complete.prefix journal)
  ... | nothing with confirmed
  ... | ()
  admittedDone observed token candidateKey requested before journal raw confirmed | nothing | just next
    with Plan.Step.id next ≟Text Plan.Step.id (declared candidateKey)
  ... | no _ with confirmed
  ... | ()
  admittedDone observed token candidateKey requested before journal raw confirmed | nothing | just next | yes _ =
    freshDone observed token candidateKey requested before raw saved confirmed

  executeDone : ∀ observed token candidateKey before raw → proj₂ (execute observed token candidateKey before) ≡ Step.done raw →
    Store.lookupSaved (proj₁ (execute observed token candidateKey before)) token (Plan.Step.id (declared candidateKey)) ≡ just raw
  executeDone observed token candidateKey before raw confirmed with Final.original token (Step.registration before)
  ... | inj₁ _ with confirmed
  ... | ()
  executeDone observed token candidateKey before raw confirmed | inj₂ (requested , _) with Store.lookupCancellation before token
  ... | just _ with confirmed
  ... | ()
  executeDone observed token candidateKey before raw confirmed | inj₂ (requested , _) | nothing
    with J.check token before (Final.ownerSteps (Input.Review.candidates (Review.Request.original requested)))
  ... | inj₁ _ with confirmed
  ... | ()
  executeDone observed token candidateKey before raw confirmed | inj₂ (requested , _) | nothing | inj₂ journal
    with addressing? (Final.ownerSteps (Input.Review.candidates (Review.Request.original requested)))
  ... | no _ with confirmed
  ... | ()
  executeDone observed token candidateKey before raw confirmed | inj₂ (requested , _) | nothing | inj₂ journal | yes _ =
    admittedDone observed token candidateKey requested before journal raw confirmed

  data OwnerPause (token : ℕ) (requested : Review.Request) (observed : AllocationObservation) (before : Store.World) :
    Step.Result Validation.Fault → Set where
    cancellationObserved : ∀ receipt → Store.lookupCancellation before token ≡ just receipt → OwnerPause token requested observed before (Step.cancelled receipt)
    sourceRefused : ∀ fault → sourceProject requested before ≡ inj₁ fault → OwnerPause token requested observed before (Step.needsInput fault)
    allocationUnavailable : ∀ fault → observed ≡ unavailable fault → OwnerPause token requested observed before (Step.needsInput fault)
    projectRefused : ∀ receipt project → observed ≡ allocated receipt → sourceProject requested before ≡ inj₂ project →
      Allocation.project (AllocationReceipt.value receipt) ≢ project → OwnerPause token requested observed before (Step.needsInput wrongProject)

  data OwnerLegal (token : ℕ) (requested : Review.Request) (candidateKey : Text) (observed : AllocationObservation) (before : Store.World) :
    Store.World → Step.Result Validation.Fault → Set where
    readable : ∀ raw value after → Store.lookupSaved after token (Plan.Step.id (declared candidateKey)) ≡ just raw →
      Saved.read raw ≡ inj₂ value → OwnerLegal token requested candidateKey observed before after (Step.done raw)
    paused : ∀ reply → OwnerPause token requested observed before reply → OwnerLegal token requested candidateKey observed before before reply

  freshLegal : ∀ observed token candidateKey requested before →
    Store.lookupSaved before token (Plan.Step.id (declared candidateKey)) ≡ nothing →
    OwnerLegal token requested candidateKey observed before (proj₁ (fresh observed token candidateKey requested before))
      (proj₂ (fresh observed token candidateKey requested before))
  freshLegal observed token candidateKey requested before absent with sourceProject requested before in source
  ... | inj₁ fault = paused _ (sourceRefused fault source)
  ... | inj₂ project with observed
  ... | unavailable fault = paused _ (allocationUnavailable fault refl)
  ... | allocated receipt with Allocation.project (AllocationReceipt.value receipt) ≟Text project
  ... | no different = paused _ (projectRefused receipt project refl source different)
  ... | yes _ = readable _ _ _
    (publicationReadable token (Plan.Step.id (declared candidateKey)) (AllocationReceipt.value receipt)
      (Enc.answer (AllocationReceipt.value receipt)) before absent) (AllocationReceipt.decoded receipt)

  justStepSame : ∀ {first second : Plan.Step} → just first ≡ just second → first ≡ second
  justStepSame refl = refl

  admittedLegal : ∀ observed token candidateKey requested before journal rest →
    J.Cursor token before (Final.ownerSteps (Input.Review.candidates (Review.Request.original requested))) (declared candidateKey ∷ rest) →
    OwnerLegal token requested candidateKey observed before
      (proj₁ (admittedOwner observed token candidateKey requested before journal))
      (proj₂ (admittedOwner observed token candidateKey requested before journal))
  admittedLegal observed token candidateKey requested before journal rest cursor
    with Store.lookupSaved before token (Plan.Step.id (declared candidateKey)) in saved
  ... | just raw with J.cursorDecoded token before _ (declared candidateKey) rest raw (J.Complete.prefix journal) cursor saved
  ... | value , decoded = readable raw value before saved decoded
  admittedLegal observed token candidateKey requested before journal rest cursor | nothing
    with J.next (J.Complete.prefix journal) in selected
  ... | nothing with trans (sym selected) (J.cursorNext token before _ _ rest (J.Complete.prefix journal) cursor saved)
  ... | ()
  admittedLegal observed token candidateKey requested before journal rest cursor | nothing | just next
    with Plan.Step.id next ≟Text Plan.Step.id (declared candidateKey)
  ... | no wrong = ⊥-elim (wrong (cong Plan.Step.id (justStepSame
    (trans (sym selected) (J.cursorNext token before _ _ rest (J.Complete.prefix journal) cursor saved)))))
  ... | yes _ = freshLegal observed token candidateKey requested before saved

  executeLegal : ∀ observed token candidateKey requested time before →
    Final.original token (Step.registration before) ≡ inj₂ (requested , time) →
    J.Complete token before (Final.ownerSteps (Input.Review.candidates (Review.Request.original requested))) →
    Addressing (Final.ownerSteps (Input.Review.candidates (Review.Request.original requested))) →
    (rest : List Plan.Step) → J.Cursor token before (Final.ownerSteps (Input.Review.candidates (Review.Request.original requested))) (declared candidateKey ∷ rest) →
    OwnerLegal token requested candidateKey observed before (proj₁ (execute observed token candidateKey before))
      (proj₂ (execute observed token candidateKey before))
  executeLegal observed token candidateKey requested time before original initial addresses rest cursor rewrite original
    with Store.lookupCancellation before token in cancellation
  ... | just receipt = paused _ (cancellationObserved receipt cancellation)
  ... | nothing with J.check token before (Final.ownerSteps (Input.Review.candidates (Review.Request.original requested))) in checked
  ... | inj₁ fault = ⊥-elim (J.checkCannotFail token before _ initial fault checked)
  ... | inj₂ journal with addressing? (Final.ownerSteps (Input.Review.candidates (Review.Request.original requested)))
  ... | no incorrect = ⊥-elim (incorrect addresses)
  ... | yes _ = admittedLegal observed token candidateKey requested before journal rest cursor

  data Recorded (token : ℕ) (before : Store.World) : List (Text × Store.EmbeddingOwnerRow) → Set where
    noOwners : Recorded token before []
    recorded : ∀ candidateKey value raw rest →
      Store.lookupSaved before token (Plan.Step.id (declared candidateKey)) ≡ just raw → Saved.read raw ≡ inj₂ value →
      Recorded token before rest → Recorded token before ((candidateKey , owner token value) ∷ rest)

  keepRecorded : ∀ token before after rows →
    (∀ key raw → Store.lookupSaved before token key ≡ just raw → Store.lookupSaved after token key ≡ just raw) →
    Recorded token before rows → Recorded token after rows
  keepRecorded token before after [] kept noOwners = noOwners
  keepRecorded token before after .((candidateKey , owner token value) ∷ rest) kept
    (recorded candidateKey value raw rest known decoded rows) =
    recorded candidateKey value raw rest (kept (Plan.Step.id (declared candidateKey)) raw known) decoded
      (keepRecorded token before after rest kept rows)

  appendRecorded : ∀ token before first second → Recorded token before first → Recorded token before second → Recorded token before (first ++ second)
  appendRecorded token before [] second noOwners later = later
  appendRecorded token before .((candidateKey , owner token value) ∷ rest) second
    (recorded candidateKey value raw rest known decoded earlier) later =
    recorded candidateKey value raw (rest ++ second) known decoded (appendRecorded token before rest second earlier later)

  data OwnersExtended (token : ℕ) (original : List Store.EmbeddingOwnerRow) : List Store.EmbeddingOwnerRow → Set where
    sameOwners : OwnersExtended token original original
    moreOwner : ∀ value current → OwnersExtended token original current → OwnersExtended token original (owner token value ∷ current)

  record Frame (token : ℕ) (before after : Store.World) : Set where
    field business : protected after ≡ protected before
          originalRegistration : Step.registration after ≡ Step.registration before
          originalAnswers : ∀ queried key raw → Store.lookupSaved before queried key ≡ just raw →
            Store.lookupSaved after queried key ≡ just raw
          originalOwners : OwnersExtended token (Store.World.embeddingOwners before) (Store.World.embeddingOwners after)
          validPrefix : ∀ requested time → Final.original token (Step.registration before) ≡ inj₂ (requested , time) →
            J.Complete token before (Final.ownerSteps (Input.Review.candidates (Review.Request.original requested))) →
            J.Complete token after (Final.ownerSteps (Input.Review.candidates (Review.Request.original requested)))

  identityFrame : ∀ token before → Frame token before before
  identityFrame token before = record
    { business = refl; originalRegistration = refl; originalAnswers = λ _ _ _ known → known
    ; originalOwners = sameOwners; validPrefix = λ _ _ _ journal → journal }

  changeKeepsJournal : ∀ token before after → Change token before after →
    ∀ requested time → Final.original token (Step.registration before) ≡ inj₂ (requested , time) →
    J.Complete token before (Final.ownerSteps (Input.Review.candidates (Review.Request.original requested))) →
    J.Complete token after (Final.ownerSteps (Input.Review.candidates (Review.Request.original requested)))
  changeKeepsJournal token before .before stayed requested time original journal = journal
  changeKeepsJournal token before _ (added actual received original journal addresses next selected receipt source)
    requested time wanted initial with trans (sym original) wanted
  ... | refl = J.extendComplete token before _ initial next (AllocationReceipt.value receipt)
    (Enc.answer (AllocationReceipt.value receipt)) addresses
    (trans (J.sameNext (J.Complete.prefix initial) (J.Complete.prefix journal)) selected)
    (AllocationReceipt.decoded receipt)

  changeFrame : ∀ token before after → Change token before after → Frame token before after
  changeFrame token before .before stayed = identityFrame token before
  changeFrame token before after changed@(added requested time original journal addresses next selected receipt source) = record
    { business = publicationKeepsProtected token (Plan.Step.id next) value raw before
    ; originalRegistration = publicationKeepsRegistration token (Plan.Step.id next) value raw before
    ; originalAnswers = publicationKeepsOldAnswer token (Plan.Step.id next) value raw before
    ; originalOwners = subst (OwnersExtended token (Store.World.embeddingOwners before))
        (sym (publicationOwners token (Plan.Step.id next) value raw before)) (moreOwner value _ sameOwners)
    ; validPrefix = changeKeepsJournal token before after changed }
    where value = AllocationReceipt.value receipt; raw = Enc.answer value

  extendOwners : ∀ token first middle final → OwnersExtended token first middle → OwnersExtended token middle final →
    OwnersExtended token first final
  extendOwners token first middle .middle earlier sameOwners = earlier
  extendOwners token first middle _ earlier (moreOwner value current later) =
    moreOwner value current (extendOwners token first middle current earlier later)

  composeFrame : ∀ token first middle final → Frame token first middle → Frame token middle final → Frame token first final
  composeFrame token first middle final earlier later = record
    { business = trans (Frame.business later) (Frame.business earlier)
    ; originalRegistration = trans (Frame.originalRegistration later) (Frame.originalRegistration earlier)
    ; originalAnswers = λ queried key raw known → Frame.originalAnswers later queried key raw
        (Frame.originalAnswers earlier queried key raw known)
    ; originalOwners = extendOwners token _ _ _ (Frame.originalOwners earlier) (Frame.originalOwners later)
    ; validPrefix = λ requested time original journal → Frame.validPrefix later requested time
        (trans (cong (Final.original token) (Frame.originalRegistration earlier)) original)
        (Frame.validPrefix earlier requested time original journal) }

  freshPhysical : ∀ observed token candidateKey requested before →
    DB.Atomic before (proj₁ (fresh observed token candidateKey requested before))
      (Step.receiptFor (proj₂ (fresh observed token candidateKey requested before)))
      (proj₁ (fresh observed token candidateKey requested before))
  freshPhysical observed token candidateKey requested before with sourceProject requested before
  ... | inj₁ _ = DB.abortedNone
  ... | inj₂ project with observed
  ... | unavailable _ = DB.abortedNone
  ... | allocated receipt with Allocation.project (AllocationReceipt.value receipt) ≟Text project
  ... | no _ = DB.abortedNone
  ... | yes _ = DB.committedAll

  admittedPhysical : ∀ observed token candidateKey requested before journal →
    DB.Atomic before (proj₁ (admittedOwner observed token candidateKey requested before journal))
      (Step.receiptFor (proj₂ (admittedOwner observed token candidateKey requested before journal)))
      (proj₁ (admittedOwner observed token candidateKey requested before journal))
  admittedPhysical observed token candidateKey requested before journal
    with Store.lookupSaved before token (Plan.Step.id (declared candidateKey))
  ... | just _ = DB.committedAll
  ... | nothing with J.next (J.Complete.prefix journal)
  ... | nothing = DB.abortedNone
  ... | just next with Plan.Step.id next ≟Text Plan.Step.id (declared candidateKey)
  ... | no _ = DB.abortedNone
  ... | yes _ = freshPhysical observed token candidateKey requested before

  expectedPhysical : ∀ observed token candidateKey before → DB.Atomic before
    (proj₁ (execute observed token candidateKey before))
    (Step.receiptFor (proj₂ (execute observed token candidateKey before)))
    (proj₁ (execute observed token candidateKey before))
  expectedPhysical observed token candidateKey before with Final.original token (Step.registration before)
  ... | inj₁ _ = DB.abortedNone
  ... | inj₂ (requested , _) with Store.lookupCancellation before token
  ... | just _ = DB.abortedNone
  ... | nothing with J.check token before (Final.ownerSteps (Input.Review.candidates (Review.Request.original requested)))
  ... | inj₁ _ = DB.abortedNone
  ... | inj₂ journal with addressing? (Final.ownerSteps (Input.Review.candidates (Review.Request.original requested)))
  ... | no _ = DB.abortedNone
  ... | yes _ = admittedPhysical observed token candidateKey requested before journal

  data Effect : Set where
    inspectOwners : ℕ → Effect
    reserve : ℕ → Text → Effect

  Reply : Effect → Set
  Reply (inspectOwners _) = Wire.Value × Store.World
  Reply (reserve _ _) = AllocationObservation × Step.Result Validation.Fault

  Atomic : Store.World → (effect : Effect) → Reply effect → Store.World → Set
  Atomic before (inspectOwners token) (current , snapshot) after = snapshot ≡ before × after ≡ before
  Atomic before (reserve token candidateKey) (observed , reply) after =
    reply ≡ proj₂ (execute observed token candidateKey before) ×
      DB.Atomic before (proj₁ (execute observed token candidateKey before)) (Step.receiptFor reply) after

  knownPhysicalUnique : ∀ (before proposed first second : Store.World) (reply : Step.Result Validation.Fault) →
    DB.Atomic before proposed (Step.receiptFor reply) first → DB.Atomic before proposed (Step.receiptFor reply) second → first ≡ second
  knownPhysicalUnique before proposed .proposed .proposed (Step.done _) DB.committedAll DB.committedAll = refl
  knownPhysicalUnique before proposed .before .before (Step.needsInput _) DB.abortedNone DB.abortedNone = refl
  knownPhysicalUnique before proposed .before .before Step.needsRecovery DB.abortedNone DB.abortedNone = refl
  knownPhysicalUnique before proposed .before .before (Step.cancelled _) DB.abortedNone DB.abortedNone = refl

  ownerObservation : ∀ token candidateKey observed reply before after →
    Atomic before (reserve token candidateKey) (observed , reply) after → (after , reply) ≡ execute observed token candidateKey before
  ownerObservation token candidateKey observed .(proj₂ (execute observed token candidateKey before)) before after (refl , physical) =
    cong (λ world → world , proj₂ (execute observed token candidateKey before))
      (knownPhysicalUnique before _ after _ _ physical (expectedPhysical observed token candidateKey before))

  effectToken : Effect → ℕ
  effectToken (inspectOwners token) = token
  effectToken (reserve token _) = token

  atomicFrame : ∀ before effect reply after → Atomic before effect reply after → Frame (effectToken effect) before after
  atomicFrame before (inspectOwners token) (current , .before) .before (refl , refl) = identityFrame token before
  atomicFrame before (reserve token candidateKey) (observed , reply) after physical =
    subst (Frame token before) (sym (cong proj₁ (ownerObservation token candidateKey observed reply before after physical)))
      (changeFrame token before _ (executeChange observed token candidateKey before))

  module X = Recovery.Execution Store.World Effect Reply Atomic
  module E = X.E

  walk : ℕ → Review.Request → List Text → List (Text × Store.EmbeddingOwnerRow) → E.Script Result
  afterOwner : ℕ → Review.Request → Text → List Text → List (Text × Store.EmbeddingOwnerRow) →
    AllocationObservation × Step.Result Validation.Fault → E.Script Result
  walk token requested [] earlier = E.done (ready (context token requested earlier))
  walk token requested (candidateKey ∷ rest) earlier =
    E.ask (reserve token candidateKey) (afterOwner token requested candidateKey rest earlier)
  afterOwner token requested candidateKey rest earlier (observed , Step.done raw) with Saved.read raw
  ... | inj₁ fault = E.done (stopped (Step.needsInput fault))
  ... | inj₂ value = walk token requested rest (earlier ++ ((candidateKey , owner token value) ∷ []))
  afterOwner token requested candidateKey rest earlier (observed , Step.needsInput fault) = E.done (stopped (Step.needsInput fault))
  afterOwner token requested candidateKey rest earlier (observed , Step.needsRecovery) = E.done (stopped Step.needsRecovery)
  afterOwner token requested candidateKey rest earlier (observed , Step.cancelled cancellation) = E.done (stopped (Step.cancelled cancellation))

  afterInspection : ℕ → Wire.Value × Store.World → E.Script Result
  afterInspection token (current , snapshot) with inspect current token snapshot
  ... | stop reply = E.done (stopped reply)
  ... | run requested = walk token requested (keys (Input.Review.candidates (Review.Request.original requested))) []

  script : ℕ → E.Script Result
  script token = E.ask (inspectOwners token) (afterInspection token)

  data Scoped (token : ℕ) : E.Script Result → Set where
    returned : ∀ reply → Scoped token (E.done reply)
    asked : ∀ effect continuation → effectToken effect ≡ token →
      (∀ reply → Scoped token (continuation reply)) → Scoped token (E.ask effect continuation)

  walkScoped : ∀ token requested remaining earlier → Scoped token (walk token requested remaining earlier)
  afterOwnerScoped : ∀ token requested candidateKey rest earlier observed →
    Scoped token (afterOwner token requested candidateKey rest earlier observed)
  walkScoped token requested [] earlier = returned _
  walkScoped token requested (candidateKey ∷ rest) earlier = asked _ _ refl (afterOwnerScoped token requested candidateKey rest earlier)
  afterOwnerScoped token requested candidateKey rest earlier (observed , Step.done raw) with Saved.read raw
  ... | inj₁ _ = returned _
  ... | inj₂ value = walkScoped token requested rest (earlier ++ ((candidateKey , owner token value) ∷ []))
  afterOwnerScoped token requested candidateKey rest earlier (observed , Step.needsInput _) = returned _
  afterOwnerScoped token requested candidateKey rest earlier (observed , Step.needsRecovery) = returned _
  afterOwnerScoped token requested candidateKey rest earlier (observed , Step.cancelled _) = returned _

  afterInspectionScoped : ∀ token observed → Scoped token (afterInspection token observed)
  afterInspectionScoped token (current , snapshot) with inspect current token snapshot
  ... | stop _ = returned _
  ... | run requested = walkScoped token requested _ []

  scriptScoped : ∀ token → Scoped token (script token)
  scriptScoped token = asked _ _ refl (afterInspectionScoped token)

  prefixScoped : ∀ token program events residual → Scoped token program → E.Prefix program events residual →
    All (λ event → effectToken (proj₁ event) ≡ token) events × Scoped token residual
  prefixScoped token program [] .program scoped (E.stopped _) = [] , scoped
  prefixScoped token .(E.ask effect continuation) .((effect , reply) ∷ events) residual
    (asked effect continuation owned later) (E.replied _ _ reply {events} prefix)
    with prefixScoped token (continuation reply) events residual (later reply) prefix
  ... | owners , scoped = (owned ∷ owners) , scoped

  changesFrame : ∀ token before events after → All (λ event → effectToken (proj₁ event) ≡ token) events →
    X.Changes before events after → Frame token before after
  changesFrame token before [] .before [] (X.unchanged _) = identityFrame token before
  changesFrame token before ((effect , reply) ∷ events) after (owned ∷ owners)
    (X.changed .before .effect .reply middle physical later) = composeFrame token before middle after
      (subst (λ identity → Frame identity before middle) owned (atomicFrame before effect reply middle physical))
      (changesFrame token middle events after owners later)

  interruptedFrame : ∀ token initial interrupted → X.Interrupted (script token) initial interrupted → Frame token initial interrupted
  interruptedFrame token initial interrupted (X.atPrefix events residual .interrupted prefix changes)
    with prefixScoped token (script token) events residual (scriptScoped token) prefix
  ... | owners , _ = changesFrame token initial events interrupted owners changes
  interruptedFrame token initial interrupted (X.beforeReply events effect continuation current reply .interrupted prefix changes physical)
    with prefixScoped token (script token) events (E.ask effect continuation) (scriptScoped token) prefix
  ... | owners , asked .effect .continuation owned later = composeFrame token initial current interrupted
    (changesFrame token initial events current owners changes)
    (subst (λ identity → Frame identity current interrupted) owned (atomicFrame current effect reply interrupted physical))

  completedFrame : ∀ token initial final reply → X.Completed (script token) initial final reply → Frame token initial final
  completedFrame token initial final reply completion = interruptedFrame token initial final
    (X.completedRunMayLoseFinalReply (script token) initial final reply completion)

  afterCompletedReadback : ∀ token current before binding reply →
    Readback.admission (toList "review_experience") token before ≡ Readback.returned (Readback.completed binding reply) →
    afterInspection token (current , before) ≡ E.done (stopped (Step.done reply))
  afterCompletedReadback token current before binding reply completedOutcome rewrite completedOutcome = refl

  returnedObservation : ∀ (initial final : Store.World) (expected actual : Result) (events : List E.Event) → E.Runs (E.done expected) events actual →
    X.Changes initial events final → final ≡ initial × actual ≡ expected
  returnedObservation initial .initial expected .expected [] (E.returned _) (X.unchanged _) = refl , refl

  completedReadback : ∀ token before binding reply →
    Readback.admission (toList "review_experience") token before ≡ Readback.returned (Readback.completed binding reply) →
    ∀ final result → X.Completed (script token) before final result →
    final ≡ before × result ≡ stopped (Step.done reply)
  completedReadback token before binding reply completedOutcome final result
    (X.completed .((inspectOwners token , current , before) ∷ events)
      (E.replied _ _ (current , .before) {events} later)
      (X.changed .before _ _ .before (refl , refl) changes)) =
    returnedObservation before final (stopped (Step.done reply)) result events
      (subst (λ program → E.Runs program events result)
        (afterCompletedReadback token current before binding reply completedOutcome) later) changes

  -- Suppliers are used only to exhibit an available execution. Atomic accepts
  -- the actual observed settings/PG replies, including different uncommitted
  -- observations on a retry. They assert no application goal or journal law.
  record Environment : Set where
    field currentSettings : ℕ → Store.World → Wire.Value
          observeAllocation : ℕ → Text → Store.World → AllocationObservation

  walkProgress : (environment : Environment) → ∀ token requested remaining earlier before →
    Σ Store.World (λ final → Σ Result (λ reply → X.Completed (walk token requested remaining earlier) before final reply))
  afterOwnerProgress : (environment : Environment) → ∀ token requested candidateKey rest earlier observed before →
    Σ Store.World (λ final → Σ Result (λ reply → X.Completed (afterOwner token requested candidateKey rest earlier observed) before final reply))
  walkProgress environment token requested [] earlier before = before , ready (context token requested earlier) ,
    X.completed [] (E.returned _) (X.unchanged before)
  walkProgress environment token requested (candidateKey ∷ rest) earlier before
    with afterOwnerProgress environment token requested candidateKey rest earlier
      (Environment.observeAllocation environment token candidateKey before , proj₂ (execute (Environment.observeAllocation environment token candidateKey before) token candidateKey before))
      (proj₁ (execute (Environment.observeAllocation environment token candidateKey before) token candidateKey before))
  ... | final , reply , X.completed events execution changes = final , reply , X.completed
    ((reserve token candidateKey , observed , proj₂ expected) ∷ events)
    (E.replied _ _ (observed , proj₂ expected) execution)
    (X.changed before _ _ _ (refl , expectedPhysical observed token candidateKey before) changes)
    where observed = Environment.observeAllocation environment token candidateKey before
          expected = execute observed token candidateKey before
  afterOwnerProgress environment token requested candidateKey rest earlier (observed , Step.done raw) before with Saved.read raw
  ... | inj₁ fault = before , stopped (Step.needsInput fault) , X.completed [] (E.returned _) (X.unchanged before)
  ... | inj₂ value = walkProgress environment token requested rest (earlier ++ ((candidateKey , owner token value) ∷ [])) before
  afterOwnerProgress environment token requested candidateKey rest earlier (observed , Step.needsInput fault) before =
    before , stopped (Step.needsInput fault) , X.completed [] (E.returned _) (X.unchanged before)
  afterOwnerProgress environment token requested candidateKey rest earlier (observed , Step.needsRecovery) before =
    before , stopped Step.needsRecovery , X.completed [] (E.returned _) (X.unchanged before)
  afterOwnerProgress environment token requested candidateKey rest earlier (observed , Step.cancelled cancellation) before =
    before , stopped (Step.cancelled cancellation) , X.completed [] (E.returned _) (X.unchanged before)

  inspectionProgress : (environment : Environment) → ∀ token observed before →
    Σ Store.World (λ final → Σ Result (λ reply → X.Completed (afterInspection token observed) before final reply))
  inspectionProgress environment token (current , snapshot) before with inspect current token snapshot
  ... | stop reply = before , stopped reply , X.completed [] (E.returned _) (X.unchanged before)
  ... | run requested = walkProgress environment token requested (keys (Input.Review.candidates (Review.Request.original requested))) [] before

  progress : (environment : Environment) → ∀ token before →
    Σ Store.World (λ final → Σ Result (λ reply → X.Completed (script token) before final reply))
  progress environment token before with inspectionProgress environment token (Environment.currentSettings environment token before , before) before
  ... | final , reply , X.completed events execution changes = final , reply , X.completed
    ((inspectOwners token , (Environment.currentSettings environment token before , before)) ∷ events)
    (E.replied _ _ _ execution) (X.changed before _ _ before (refl , refl) changes)
