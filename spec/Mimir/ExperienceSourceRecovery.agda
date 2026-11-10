{-# OPTIONS --safe #-}
-- Revision admission and source publication are derived from the original
-- request, complete world and observed PostgreSQL item allocations.
module Mimir.ExperienceSourceRecovery where

open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Float.Base using (Float)
open import Data.Integer using (ℤ; +_; ∣_∣) renaming (_-_ to _-ℤ_)
import Data.Integer.Properties as Integer
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Properties as Maybes
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.LearningStore as Learning
import Mimir.ExperienceSchema as Source
import Mimir.ExperienceRecord as Recording
import Mimir.ExperienceRead as Read
import Mimir.LearningInput as Input
import Mimir.LearningOperations as Operations
import Mimir.ExperienceSourceIntent as Intent
import Mimir.ReviewObservation as Observation
import Mimir.ReviewPreparationPublication as Publication
import Mimir.LearningCorrections as Corrections
import Mimir.LearningKeys as Keys
import Mimir.SemanticKey as Key
import Mimir.LearningTargets as Targets
import Mimir.LearningRecompute as Recompute
import Mimir.PosteriorComputation as Posterior
import Mimir.PublicEncoding as Encoding
import Mimir.StructuredValue as Wire
import Mimir.Validation as Validation
import Mimir.RecoverableStoreStep as Step
import Mimir.RegisteredStoreAdmission as Admission
import Mimir.StandardLibrary as Conversion
import Mimir.LearningWire as LearningWire
import Mimir.PublicInput as Public
import Mimir.RecordDecoding as Decode
import Mimir.JsonObjects as Objects
import Mimir.Binary64 as Binary
import Mimir.Recovery as Recovery
import Mimir.DatabaseTransaction as DB
import Mimir.LearningCandidates as Candidates
import Mimir.SourceSchema as Sources
open import Mimir.RecordDecoding using (_>>=_)

record Request : Set where
  constructor request
  field source : Input.Experience; expected : ℤ

record Metadata : Set where
  constructor observed
  field sourceTime : ℤ; posteriorTime : ℤ; itemReplies : List (Operations.Failure ⊎ ℕ)

-- External observation capability, not an application UUID generator or an
-- axiom about the desired world. Convergence permits every observed reply,
-- independently of the particular capability used to exhibit progress.
record PostgreSQL : Set where
  field clock : ℕ → Store.World → ℤ
        itemReply : ℕ → Text → Text → Text → Operations.Failure ⊎ ℕ

data Selection : Set where
  refused : Recording.Failure → Selection
  replay : Observation.Snapshot → Selection
  fresh : ℕ → Selection

references : Store.World → Source.Experience → ℕ → Selection
references before value expected with Validation.at (Validation.key "experience")
  (Validation.at (Validation.key "belief_ids") (Targets.validate (Source.Experience.project value)
    (map Recompute.target (Store.beliefs before)) (Source.Experience.beliefIDs value)))
... | Validation.rejected fault _ = refused (Recording.invalid fault)
... | Validation.accepted _ with Source.Experience.patternID value
... | nothing = fresh expected
... | just identity with Recording.patternAllowed (Source.Experience.project value) identity (Store.nodes before)
... | nothing = refused Recording.missingPattern
... | just false = refused Recording.foreignPattern
... | just true = fresh expected

existing : Store.World → Source.Experience → ℤ → Observation.Snapshot → Selection
existing before value expected old with Observation.checkSnapshot old
... | Validation.rejected fault _ = refused (Recording.invalid fault)
... | Validation.accepted _ with Recording.coherent (Store.World.learning before) old
... | false = refused Recording.incoherentSnapshot
... | true with Validation.at (Validation.key "experience")
  (Corrections.validateExperienceCorrection (Observation.Snapshot.experience old) value)
... | Validation.rejected fault _ = refused (Recording.invalid fault)
... | Validation.accepted _ with
  does (Key.equal (Keys.experience (Observation.Snapshot.experience old)) (Keys.experience value)) ∧
    (does (expected Integer.≟ Observation.Snapshot.revision old) ∨
      does (expected Integer.≟ (Observation.Snapshot.revision old -ℤ (+ 1))))
... | true = replay old
... | false with expected Integer.≟ Observation.Snapshot.revision old
... | no _ = refused Recording.staleRevision
... | yes _ = references before value ∣ expected ∣

select : Store.World → Source.Experience → ℤ → Selection
select before value expected with Validation.at (Validation.key "experience") (Source.validate value)
... | Validation.rejected fault _ = refused (Recording.invalid fault)
... | Validation.accepted _ with Operations.expectedValid expected
... | false = refused Recording.invalidExpected
... | true with Read.get (Source.Experience.identity value) (Learning.World.current (Store.World.learning before))
... | just old = existing before value expected old
... | nothing with expected Integer.≟ (+ 0)
... | no _ = refused Recording.staleRevision
... | yes _ = references before value 0

module Business (database : ℕ) (format : Encoding.Formatting)
  (databaseSum : List Float → Float) (calculator : Posterior.Calculator) where
  module M = Intent.For database format databaseSum calculator

  Diagnostic = Validation.Fault ⊎ (Recording.Failure ⊎ (Operations.Failure ⊎ M.B.Diagnostic))
  Outcome = Diagnostic ⊎ (Store.World × Wire.Value)
  requestFault : Validation.Fault → Diagnostic
  requestFault = inj₁
  sourceFailure : Recording.Failure → Diagnostic
  sourceFailure failure = inj₂ (inj₁ failure)
  allocationFailure : Operations.Failure → Diagnostic
  allocationFailure failure = inj₂ (inj₂ (inj₁ failure))
  numericalFailure : M.B.Diagnostic → Diagnostic
  numericalFailure failure = inj₂ (inj₂ (inj₂ failure))

  incomplete : Validation.Fault
  incomplete = Validation.fault (Validation.key "allocation_receipt" ∷ []) Validation.malformedInput
    "The source allocation observation is incomplete. Read this token's saved outcome and diagnostics; do not invent an item UUID or repeat a possibly committed write."

  mapNumerical : M.Outcome → Outcome
  mapNumerical (inj₁ diagnostic) = inj₁ (numericalFailure diagnostic)
  mapNumerical (inj₂ publication) = inj₂ publication

  NumericalGoal : Source.Experience → ℕ → Metadata → ℤ → Store.World → Outcome → Set
  NumericalGoal value expected metadata posteriorTime before (inj₁ (inj₂ (inj₂ (inj₂ diagnostic)))) =
    M.Goal value expected (Metadata.sourceTime metadata) posteriorTime before (inj₁ diagnostic)
  NumericalGoal value expected metadata posteriorTime before (inj₁ _) = ⊥
  NumericalGoal value expected metadata posteriorTime before (inj₂ publication) =
    M.Goal value expected (Metadata.sourceTime metadata) posteriorTime before (inj₂ publication)

  checkedNumerical : ∀ value expected metadata posteriorTime before →
    Σ Outcome (NumericalGoal value expected metadata posteriorTime before)
  checkedNumerical value expected metadata posteriorTime before = convert
    (M.checked value expected (Metadata.sourceTime metadata) posteriorTime before)
    where
    convert : Σ M.Outcome (M.Goal value expected (Metadata.sourceTime metadata) posteriorTime before) →
      Σ Outcome (NumericalGoal value expected metadata posteriorTime before)
    convert (inj₁ diagnostic , correct) = inj₁ (numericalFailure diagnostic) , correct
    convert (inj₂ publication , correct) = inj₂ publication , correct

  SelectedGoal : Source.Experience → Metadata → ℤ → Store.World → Store.World → Selection → Outcome → Set
  SelectedGoal canonical metadata posteriorTime before staged (refused failure) outcome = outcome ≡ inj₁ (sourceFailure failure)
  SelectedGoal canonical metadata posteriorTime before staged (replay original) outcome = outcome ≡ inj₂ (before , M.sourceReply original)
  SelectedGoal canonical metadata posteriorTime before staged (fresh expected) outcome =
    NumericalGoal canonical expected metadata posteriorTime staged outcome

  selectedChecked : ∀ canonical metadata posteriorTime before staged selected →
    Σ Outcome (SelectedGoal canonical metadata posteriorTime before staged selected)
  selectedChecked canonical metadata posteriorTime before staged (refused failure) = inj₁ (sourceFailure failure) , refl
  selectedChecked canonical metadata posteriorTime before staged (replay original) = inj₂ (before , M.sourceReply original) , refl
  selectedChecked canonical metadata posteriorTime before staged (fresh expected) =
    checkedNumerical canonical expected metadata posteriorTime staged

  NormalizationGoal : Request → Metadata → ℤ → Store.World → M.NormalizationResult → Outcome → Set
  NormalizationGoal input metadata posteriorTime before nothing outcome = outcome ≡ inj₁ (requestFault incomplete)
  NormalizationGoal input metadata posteriorTime before (just (inj₁ failure)) outcome = outcome ≡ inj₁ (allocationFailure failure)
  NormalizationGoal input metadata posteriorTime before (just (inj₂ (staged , canonical))) outcome =
    SelectedGoal canonical metadata posteriorTime before (M.installNormalization staged before)
      (select (M.installNormalization staged before) canonical (Request.expected input)) outcome

  Goal : Request → Metadata → ℤ → Store.World → Outcome → Set
  Goal input metadata posteriorTime before = NormalizationGoal input metadata posteriorTime before
    (M.normalized (Request.source input) before (Metadata.itemReplies metadata))

  checked : ∀ input metadata posteriorTime before → Σ Outcome (Goal input metadata posteriorTime before)
  checked input metadata posteriorTime before with M.normalized (Request.source input) before (Metadata.itemReplies metadata)
  ... | nothing = inj₁ (requestFault incomplete) , refl
  ... | just (inj₁ failure) = inj₁ (allocationFailure failure) , refl
  ... | just (inj₂ (staged , canonical)) = selectedChecked canonical metadata posteriorTime before
    (M.installNormalization staged before) (select (M.installNormalization staged before) canonical (Request.expected input))

  selectedKeepsJournal : ∀ canonical metadata posteriorTime before staged selected after reply →
    Store.World.operations staged ≡ Store.World.operations before →
    SelectedGoal canonical metadata posteriorTime before staged selected (inj₂ (after , reply)) →
    Store.World.operations after ≡ Store.World.operations before
  selectedKeepsJournal canonical metadata posteriorTime before staged (refused failure) after reply same ()
  selectedKeepsJournal canonical metadata posteriorTime before staged (replay original) .before ._ same refl = refl
  selectedKeepsJournal canonical metadata posteriorTime before staged (fresh expected) after reply same correct =
    trans (M.publicationKeepsJournal canonical expected (Metadata.sourceTime metadata) posteriorTime staged after reply correct) same

  publicationKeepsJournal : ∀ input metadata posteriorTime before after reply →
    Goal input metadata posteriorTime before (inj₂ (after , reply)) → Store.World.operations after ≡ Store.World.operations before
  publicationKeepsJournal input metadata posteriorTime before after reply correct with
    M.normalized (Request.source input) before (Metadata.itemReplies metadata)
  ... | nothing with correct
  ... | ()
  publicationKeepsJournal input metadata posteriorTime before after reply correct | just (inj₁ failure) with correct
  ... | ()
  publicationKeepsJournal input metadata posteriorTime before after reply correct | just (inj₂ (staged , canonical)) =
    selectedKeepsJournal canonical metadata posteriorTime before (M.installNormalization staged before)
      (select (M.installNormalization staged before) canonical (Request.expected input)) after reply refl correct

  checkedKeepsJournal : ∀ input metadata posteriorTime before after reply →
    proj₁ (checked input metadata posteriorTime before) ≡ inj₂ (after , reply) →
    Store.World.operations after ≡ Store.World.operations before
  checkedKeepsJournal input metadata posteriorTime before after reply accepted = publicationKeepsJournal input metadata posteriorTime before after reply
    (subst (Goal input metadata posteriorTime before) accepted (proj₂ (checked input metadata posteriorTime before)))

module Registered (conversion : Conversion.Contract) (format : Encoding.Formatting) (database : ℕ)
  (databaseSum : List Float → Float) (calculator : Posterior.Calculator) (postgres : PostgreSQL) where
  module B = Business database format databaseSum calculator
  module L = LearningWire.Decode conversion (Binary.powerMinusOne 64)
  descriptor = Admission.descriptor (toList "record_experience") (toList "store.record_experience")
    (toList "[\"store.record_experience\",null]")
  key : ℕ → Text
  key _ = Admission.Descriptor.key descriptor
  distinct : ∀ token → key token ≡ Step.resultKey → ⊥
  distinct token ()

  sourceHeader : Input.Experience → Validation.Fault ⊎ Input.Experience
  sourceHeader = LearningWire.sourceHeader

  expected : ℤ → Validation.Fault ⊎ ℤ
  expected value with Operations.expectedValid value
  ... | true = inj₂ value
  ... | false = inj₁ (Validation.fault [] Validation.invalidNumber
    "Use a nonnegative current source revision with one representable increment. Read get_experience and the original token outcome; ask the user before cancelling pending work and reserving corrected arguments. Do not clamp the revision or create another incident.")

  arguments : Wire.Value → Validation.Fault ⊎ Request
  arguments = Decode.readRecord Objects.forbid Objects.rejectKnownRepeated
    (toList "experience" ∷ toList "expected_revision" ∷ []) (λ view →
      Public.required "experience" (λ raw → L.experienceInput raw >>= sourceHeader) view >>= λ value →
      Public.required "expected_revision" (λ raw → Public.i64 raw >>= expected) view >>= λ revision →
      inj₂ (request value revision))

  original : ℕ → Step.Registration → Validation.Fault ⊎ (Request × ℤ)
  original token registration with Admission.resolve descriptor token registration
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ (reserved , binding) with Store.BindingRow.settings binding
  ... | Wire.object [] = Decode.mapResult (λ input → input , Store.ReservationRow.reservedAt reserved)
    (arguments (Store.BindingRow.arguments binding))
  ... | _ = inj₁ (Validation.fault (Validation.key "settings" ∷ []) Validation.unknownField
    "record_experience has no per-request settings. Read the original binding and saved outcome; ask the user whether to cancel pending work and reserve corrected arguments. Never rewrite the bound request or choose another incident ID.")

  Internal = ℕ × Metadata
  admit : Internal → Step.Registration → Maybe B.Diagnostic
  admit (token , metadata) registration with original token registration
  ... | inj₁ fault = just (B.requestFault fault)
  ... | inj₂ _ = nothing

  decide : Internal → Store.World → B.Outcome
  decide (token , metadata) before with original token (Step.registration before)
  ... | inj₁ fault = inj₁ (B.requestFault fault)
  ... | inj₂ (input , posteriorTime) = proj₁ (B.checked input metadata (Metadata.posteriorTime metadata) before)

  keepsJournal : ∀ input before after reply → decide input before ≡ inj₂ (after , reply) →
    Store.World.operations after ≡ Store.World.operations before
  keepsJournal (token , metadata) before after reply accepted with original token (Step.registration before)
  ... | inj₁ fault with accepted
  ... | ()
  keepsJournal (token , metadata) before after reply accepted | inj₂ (input , posteriorTime) =
    B.checkedKeepsJournal input metadata (Metadata.posteriorTime metadata) before after reply accepted

  module Saved = Step.Admitted Internal B.Diagnostic proj₁ (λ input → key (proj₁ input))
    (λ input → distinct (proj₁ input)) decide keepsJournal admit
  module K = Saved.Kernel

  Present : ∀ {A : Set} → Maybe A → Set
  Present nothing = ⊥
  Present (just _) = ⊤

  -- Missing allocation observations cannot inhabit an actual completed source
  -- attempt. Readback/cancellation use their saved rows without allocating.
  Valid : ℕ → Metadata → Store.World → Set
  Valid token metadata before with original token (Step.registration before)
  ... | inj₁ _ = ⊤
  ... | inj₂ (input , _) with Store.lookupCancellation before token
  ... | just _ = ⊤
  ... | nothing with Store.lookupSaved before token (key token) | Store.lookupSaved before token Step.resultKey
  ... | nothing | nothing = Present (B.M.normalized (Request.source input) before (Metadata.itemReplies metadata))
  ... | _ | _ = ⊤

  decidesBound : ∀ token metadata before input posteriorTime →
    original token (Step.registration before) ≡ inj₂ (input , posteriorTime) →
    decide (token , metadata) before ≡ proj₁ (B.checked input metadata (Metadata.posteriorTime metadata) before)
  decidesBound token metadata before input posteriorTime bound rewrite bound = refl

  FreshGoal : ℕ → Request → Metadata → ℤ → Store.World → Store.World → Saved.Reply → Set
  FreshGoal token input metadata posteriorTime before after (Step.done reply) = Σ Store.World (λ changed →
    B.Goal input metadata posteriorTime before (inj₂ (changed , reply)) × after ≡ K.publication (token , metadata) changed reply)
  FreshGoal token input metadata posteriorTime before after (Step.needsInput diagnostic) =
    after ≡ before × B.Goal input metadata posteriorTime before (inj₁ diagnostic)
  FreshGoal token input metadata posteriorTime before after _ = ⊥

  freshMeaning : ∀ token input metadata posteriorTime before →
    original token (Step.registration before) ≡ inj₂ (input , posteriorTime) →
    FreshGoal token input metadata (Metadata.posteriorTime metadata) before (proj₁ (K.fresh (token , metadata) before)) (proj₂ (K.fresh (token , metadata) before))
  freshMeaning token input metadata posteriorTime before bound rewrite decidesBound token metadata before input posteriorTime bound
    with B.checked input metadata (Metadata.posteriorTime metadata) before
  ... | inj₁ diagnostic , correct = refl , correct
  ... | inj₂ (changed , reply) , correct = changed , correct , refl

  MetaGoal : ℕ → Metadata → Store.World → Store.World → Saved.Reply → Set
  MetaGoal token metadata before after reply with original token (Step.registration before)
  ... | inj₁ fault = after ≡ before × reply ≡ Step.needsInput (B.requestFault fault)
  ... | inj₂ (input , posteriorTime) with Store.lookupCancellation before token
  ... | just cancelled = after ≡ before × reply ≡ Step.cancelled cancelled
  ... | nothing with Store.lookupSaved before token (key token) | Store.lookupSaved before token Step.resultKey
  ... | just saved | just _ = after ≡ before × reply ≡ Step.done saved
  ... | just _ | nothing = after ≡ before × reply ≡ Step.needsRecovery
  ... | nothing | just _ = after ≡ before × reply ≡ Step.needsRecovery
  ... | nothing | nothing = FreshGoal token input metadata (Metadata.posteriorTime metadata) before after reply

  meaning : ∀ token metadata before →
    MetaGoal token metadata before (proj₁ (Saved.execute (token , metadata) before)) (proj₂ (Saved.execute (token , metadata) before))
  meaning token metadata before with original token (Step.registration before) in bound
  ... | inj₁ fault = refl , refl
  ... | inj₂ (input , posteriorTime) with Store.lookupCancellation before token
  ... | just _ = refl , refl
  ... | nothing with Store.lookupSaved before token (key token) | Store.lookupSaved before token Step.resultKey
  ... | just _ | just _ = refl , refl
  ... | just _ | nothing = refl , refl
  ... | nothing | just _ = refl , refl
  ... | nothing | nothing = freshMeaning token input metadata posteriorTime before bound

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
  Atomic before token (metadata , reply) after = Valid token metadata before ×
    Saved.Atomic before (token , metadata) reply after

  module X = Recovery.Execution Store.World Effect Reply Atomic
  module E = X.E

  script : ℕ → E.Script Saved.Reply
  script token = E.ask token (λ reply → E.done (proj₂ reply))

  atomicObservation : ∀ token before after metadata reply → Atomic before token (metadata , reply) after →
    Valid token metadata before × (after , reply) ≡ Saved.execute (token , metadata) before
  atomicObservation token before after metadata reply (valid , physical) =
    valid , Saved.atomicObservation (token , metadata) before after reply physical

  completedObservation : ∀ token before after reply → X.Completed (script token) before after reply →
    Σ Metadata (λ metadata → Valid token metadata before × (after , reply) ≡ Saved.execute (token , metadata) before)
  completedObservation token before after reply
    (X.completed _ (E.replied _ _ (metadata , _) (E.returned _))
      (X.changed _ _ _ _ physical (X.unchanged _))) =
    metadata , atomicObservation token before after metadata reply physical

  -- Refused/paused attempts have an aborted receipt and leave the starting
  -- world intact. A committed attempt carries the original saved answer.
  data InterruptOutcome (token : ℕ) (before after : Store.World) : Set where
    unchanged : after ≡ before → InterruptOutcome token before after
    published : ∀ metadata value → Valid token metadata before →
      (after , Step.done value) ≡ Saved.execute (token , metadata) before →
      InterruptOutcome token before after

  interruptedAtomic : ∀ token before after metadata reply → Atomic before token (metadata , reply) after →
    InterruptOutcome token before after
  interruptedAtomic token before after metadata (Step.done value) (valid , physical) =
    published metadata value valid (Saved.atomicObservation (token , metadata) before after (Step.done value) physical)
  interruptedAtomic token before .before metadata (Step.needsInput _) (valid , observation , DB.abortedNone) = unchanged refl
  interruptedAtomic token before .before metadata Step.needsRecovery (valid , observation , DB.abortedNone) = unchanged refl
  interruptedAtomic token before .before metadata (Step.cancelled _) (valid , observation , DB.abortedNone) = unchanged refl

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
  Goal token before after reply = Σ Metadata (λ metadata → Valid token metadata before × MetaGoal token metadata before after reply)

  fromObservation : ∀ token metadata before after reply → Valid token metadata before →
    (after , reply) ≡ Saved.execute (token , metadata) before → Goal token before after reply
  fromObservation token metadata before after reply valid observation = metadata , valid , subst
    (λ outcome → MetaGoal token metadata before (proj₁ outcome) (proj₂ outcome)) (sym observation) (meaning token metadata before)

  converges : ∀ token before interrupted after reply → X.Interrupted (script token) before interrupted →
    X.Completed (script token) interrupted after reply → Goal token before after reply
  converges token before interrupted after reply interruption completion
    with interruptionState token before interrupted interruption | completedObservation token interrupted after reply completion
  ... | unchanged refl | metadata , valid , observation = fromObservation token metadata before after reply valid observation
  ... | published first value valid same | second , _ , observation = fromObservation token first before after reply valid
    (trans observation (trans (cong (Saved.execute (token , second)) (cong proj₁ same))
      (doneStable token first second before value (sym (cong proj₂ same)))))

  -- Follow this finite allocation program with the replies of the external
  -- PostgreSQL adapter. The effect names retain the incident, local key,
  -- source reference and actor; the caller supplies none of these replies.
  collect : ∀ {A : Set} (program : B.M.T.Allocation A) →
    Σ (List (Operations.Failure ⊎ ℕ)) (λ replies → Σ A (λ value → B.M.observe program replies ≡ just value))
  collect (B.M.T.resolved value) = [] , value , refl
  collect (B.M.T.reserve incident name source actor next)
    with collect (next (PostgreSQL.itemReply postgres incident name source actor))
  ... | replies , value , resolved =
    PostgreSQL.itemReply postgres incident name source actor ∷ replies , value , resolved

  module Collected (token : ℕ) (before : Store.World) where
    allocationReplies : Request → List (Operations.Failure ⊎ ℕ)
    allocationReplies input = proj₁ (collect (B.M.Normalize.experience (Request.source input) (Store.learningView before)))

    metadata : Metadata
    metadata with original token (Step.registration before)
    ... | inj₁ _ = observed (PostgreSQL.clock postgres token before) (PostgreSQL.clock postgres token before) []
    ... | inj₂ (input , _) = observed (PostgreSQL.clock postgres token before) (PostgreSQL.clock postgres token before) (allocationReplies input)

    present : ∀ input → Present (B.M.normalized (Request.source input) before (allocationReplies input))
    present input with collect (B.M.Normalize.experience (Request.source input) (Store.learningView before))
    ... | replies , value , resolved rewrite resolved = tt

    complete : Valid token metadata before
    complete with original token (Step.registration before)
    ... | inj₁ _ = tt
    ... | inj₂ (input , _) with Store.lookupCancellation before token
    ... | just _ = tt
    ... | nothing with Store.lookupSaved before token (key token) | Store.lookupSaved before token Step.resultKey
    ... | just _ | just _ = tt
    ... | just _ | nothing = tt
    ... | nothing | just _ = tt
    ... | nothing | nothing = present input

  progress : ∀ token before → Σ Store.World (λ after → Σ Saved.Reply (λ reply → X.Completed (script token) before after reply))
  progress token before = proj₁ executionResult , proj₂ executionResult , X.completed
    ((token , metadata , proj₂ executionResult) ∷ [])
    (E.replied token (λ reply → E.done (proj₂ reply)) (metadata , proj₂ executionResult) (E.returned _))
    (X.changed before token _ _
      (Collected.complete token before , refl , Saved.expectedPhysical (token , metadata) before) (X.unchanged _))
    where
    metadata = Collected.metadata token before
    executionResult = Saved.execute (token , metadata) before

  cachedReplay : ∀ token before current raw →
    Store.lookupSaved before token Step.resultKey ≡ nothing →
    Store.lookupSaved current token Step.resultKey ≡ just raw →
    X.Interrupted (script token) before current →
    X.Completed (script token) current current (Step.done raw)
  cachedReplay token before current raw absent present cut
    with interruptionState token before current cut
  ... | unchanged same = ⊥-elim (impossible same)
    where
    impossible : current ≡ before → ⊥
    impossible refl with trans (sym absent) present
    ... | ()
  ... | published metadata value valid execution
    with Saved.doneOrigin (token , metadata) before current value (sym execution)
  ... | inj₁ same = ⊥-elim (impossible same)
    where
    impossible : current ≡ before → ⊥
    impossible refl with trans (sym absent) present
    ... | ()
  ... | inj₂ (_ , _ , final) = subst
    (λ answer → X.Completed (script token) current current (Step.done answer))
    (Maybes.just-injective (trans (sym final) present))
    (subst (λ outcome → X.Completed (script token) current (proj₁ outcome) (proj₂ outcome))
      (trans (cong (Saved.execute (token , Collected.metadata token current)) (cong proj₁ execution))
        (trans (doneStable token metadata (Collected.metadata token current) before value
          (sym (cong proj₂ execution))) (sym execution)))
      (proj₂ (proj₂ (progress token current))))

  everyDatabaseReceiptCovered : ∀ token metadata before → Valid token metadata before → ∀ tag actual →
    DB.Atomic before (proj₁ (Saved.execute (token , metadata) before)) tag actual → X.Interrupted (script token) before actual
  everyDatabaseReceiptCovered token metadata before valid .DB.committed _ DB.committedAll =
    X.beforeReply [] token (λ reply → E.done (proj₂ reply)) before
      (metadata , proj₂ (Saved.execute (token , metadata) before)) _
      (E.stopped _) (X.unchanged before) (valid , refl , Saved.expectedPhysical (token , metadata) before)
  everyDatabaseReceiptCovered token metadata before valid .DB.aborted _ DB.abortedNone =
    X.atPrefix [] (script token) before (E.stopped _) (X.unchanged before)
  everyDatabaseReceiptCovered token metadata before valid .DB.acknowledgementLost _ DB.unknownBefore =
    X.atPrefix [] (script token) before (E.stopped _) (X.unchanged before)
  everyDatabaseReceiptCovered token metadata before valid .DB.acknowledgementLost _ DB.unknownAfter =
    X.beforeReply [] token (λ reply → E.done (proj₂ reply)) before
      (metadata , proj₂ (Saved.execute (token , metadata) before)) _
      (E.stopped _) (X.unchanged before) (valid , refl , Saved.expectedPhysical (token , metadata) before)

  operation : Recovery.RecoverableFor Store.World ℕ Saved.Reply Goal
  operation = record { Effect = Effect; Reply = Reply; script = script; Atomic = Atomic; converges = converges; progress = progress }
  Result = Saved.Reply
