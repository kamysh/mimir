{-# OPTIONS --safe #-}
-- Preparation retains the first bound model and the first DURABLE capture.
-- The read-only snapshot is an observed effect; it is not an agent argument.
module Mimir.BackfillPreparationRecovery where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Relation.Nullary using (yes; no; does)
open import Data.Unit using (⊤; tt)
import Data.List.Properties as Lists
import Data.Fin.Properties as Fin
import Mimir.BackfillCaptureEncoding as CaptureEncoding
import Mimir.PublicEncoding as Encoding
import Mimir.ApplicationStore as Store
import Mimir.BackfillRecovery as Backfill
import Mimir.DatabaseTransaction as DB
import Mimir.OperationControls as Controls
import Mimir.ProjectDeletion as Project
import Mimir.RecoverableStoreStep as Step
import Mimir.RegisteredStoreAdmission as AdmissionStore
import Mimir.Recovery as Recovery
import Mimir.StandardLibrary as Library
import Mimir.StructuredValue as Wire
import Mimir.Validation as Validation

-- Settings are trusted host configuration, never an additional MCP field.
record Input : Set where
  constructor input
  field token : ℕ; settings : Wire.Value

module Preparation (library : Library.Contract) where
  module A = Backfill.Admission library
  module P = Project.Registered
  tables = Store.World.operations

  binding : ℕ → Store.World → Maybe Store.BindingRow
  binding token before = P.binding token (Store.OperationTables.bindings (tables before))
  plan : ℕ → Store.World → Maybe Wire.Value
  plan token before = P.plan token (Store.OperationTables.plans (tables before))

  mismatch unknown : Validation.Fault
  mismatch = Validation.fault [] Validation.wrongIdentity
    "Read the original reembed binding, model settings and saved result. Open the user dialog to resolve mismatched metadata; do not replace an original request or selection."
  unknown = Validation.fault [] Validation.missingReference
    "Read the original reservation using its stable request_key. Do not invent a token or start a different request to bypass a missing reservation."

  row : Input → ℤ → Store.BindingRow
  row request received = Store.bindingRow (Input.token request) (toList "reembed")
    (Wire.object []) (Input.settings request) received

  putBinding : Store.BindingRow → Store.World → Store.World
  putBinding fresh before = record before
    { operations = record (tables before)
      { bindings = fresh ∷ Store.OperationTables.bindings (tables before) } }

  putPlan : ℕ → Wire.Value → Store.World → Store.World
  putPlan token raw before = record before
    { operations = record (tables before)
      { plans = Store.planRow token raw ∷ Store.OperationTables.plans (tables before) } }

  -- Removing these TWO allowed metadata components retains the complete
  -- business world, every answer, cancellation and every other store field.
  protected : Store.World → Store.World
  protected before = record before { operations = record (tables before) { bindings = []; plans = [] } }

  bindingKeepsProtected : ∀ fresh before → protected (putBinding fresh before) ≡ protected before
  bindingKeepsProtected fresh before = refl
  planKeepsProtected : ∀ token raw before → protected (putPlan token raw before) ≡ protected before
  planKeepsProtected token raw before = refl
  protectedKeepsCapture : ∀ before → Backfill.capture (protected before) ≡ Backfill.capture before
  protectedKeepsCapture before = refl

  headBindingReadable : ∀ request received before → binding (Input.token request) (putBinding (row request received) before) ≡ just (row request received)
  headBindingReadable request received before with Input.token request ≟ Input.token request
  ... | yes _ = refl
  ... | no impossible = ⊥-elim (impossible refl)
  headPlanReadable : ∀ token raw before → plan token (putPlan token raw before) ≡ just raw
  headPlanReadable token raw before with token ≟ token
  ... | yes _ = refl
  ... | no impossible = ⊥-elim (impossible refl)

  -- The first native read chooses an existing request BEFORE consulting the
  -- current configuration. In particular an old completed result is not
  -- invalidated by a later configuration edit.
  allowed : Input → Store.World → Bool
  allowed request before with binding (Input.token request) before
  ... | nothing = A.provider (Input.settings request)
  ... | just original with Controls.Plan.textEqual (Store.BindingRow.operation original) (toList "reembed") | Store.BindingRow.arguments original
  ... | true | Wire.object [] = A.provider (Store.BindingRow.settings original)
  ... | _ | _ = false

  data Bound : Set where
    bound : Store.BindingRow → Bound
    badBinding : Validation.Fault → Bound
    cancelledBinding : Store.CancellationRow → Bound

  bind : Input → ℤ → Store.World → Store.World × Bound
  bind request received before with allowed request before
  ... | false = before , badBinding mismatch
  ... | true with AdmissionStore.reservation (Input.token request) (Store.OperationTables.reservations (tables before))
  ... | nothing = before , badBinding unknown
  ... | just _ with Store.lookupCancellation before (Input.token request)
  ... | just stopped = before , cancelledBinding stopped
  ... | nothing with binding (Input.token request) before
  ... | just original = before , bound original
  ... | nothing = putBinding (row request received) before , bound (row request received)

  bindingPreservesProtected : ∀ request received before → protected (proj₁ (bind request received before)) ≡ protected before
  bindingPreservesProtected request received before with allowed request before
  ... | false = refl
  ... | true with AdmissionStore.reservation (Input.token request) (Store.OperationTables.reservations (tables before))
  ... | nothing = refl
  ... | just _ with Store.lookupCancellation before (Input.token request)
  ... | just _ = refl
  ... | nothing with binding (Input.token request) before
  ... | just _ = refl
  ... | nothing = refl

  -- A binding extension can add this token's first request exactly once.
  -- It cannot edit an earlier timestamp/model or touch another token's row.
  data BindingsGrew (request : Input) (original : List Store.BindingRow) : List Store.BindingRow → Set where
    originalBindings : BindingsGrew request original original
    addedBinding : ∀ current received →
      P.binding (Input.token request) current ≡ nothing →
      BindingsGrew request original current →
      BindingsGrew request original (row request received ∷ current)

  bindKeepsBindings : ∀ request received original before →
    BindingsGrew request original (Store.OperationTables.bindings (tables before)) →
    BindingsGrew request original (Store.OperationTables.bindings (tables (proj₁ (bind request received before))))
  bindKeepsBindings request received original before prior with allowed request before
  ... | false = prior
  ... | true with AdmissionStore.reservation (Input.token request) (Store.OperationTables.reservations (tables before))
  ... | nothing = prior
  ... | just _ with Store.lookupCancellation before (Input.token request)
  ... | just _ = prior
  ... | nothing with binding (Input.token request) before in found
  ... | just _ = prior
  ... | nothing = addedBinding _ received found prior

  bindingKeepsPlans : ∀ request received before →
    Store.OperationTables.plans (tables (proj₁ (bind request received before))) ≡ Store.OperationTables.plans (tables before)
  bindingKeepsPlans request received before with allowed request before
  ... | false = refl
  ... | true with AdmissionStore.reservation (Input.token request) (Store.OperationTables.reservations (tables before))
  ... | nothing = refl
  ... | just _ with Store.lookupCancellation before (Input.token request)
  ... | just _ = refl
  ... | nothing with binding (Input.token request) before
  ... | just _ = refl
  ... | nothing = refl

  bindingKeepsCancellation : ∀ request received before →
    Store.lookupCancellation (proj₁ (bind request received before)) (Input.token request) ≡ Store.lookupCancellation before (Input.token request)
  bindingKeepsCancellation request received before =
    cong (λ current → Store.lookupCancellation current (Input.token request))
      (bindingPreservesProtected request received before)

  data Result : Set where
    ready : A.Context → Result
    stopped : Step.Result Validation.Fault → Result

  ReplyMeaning : Input → Store.World → Result → Set
  ReplyMeaning request before (ready selectedContext) =
    A.original (Input.token request) (Step.registration before) ≡ inj₂ selectedContext ×
    Store.lookupCancellation before (Input.token request) ≡ nothing
  ReplyMeaning request before (stopped (Step.done _)) = ⊥
  ReplyMeaning request before (stopped (Step.needsInput _)) = ⊤
  ReplyMeaning request before (stopped Step.needsRecovery) = ⊤
  ReplyMeaning request before (stopped (Step.cancelled receipt)) = Store.lookupCancellation before (Input.token request) ≡ just receipt

  canonicalReply : Validation.Fault ⊎ A.Context → Result
  canonicalReply (inj₁ fault) = stopped (Step.needsInput fault)
  canonicalReply (inj₂ selectedContext) = ready selectedContext

  canonicalMeaning : ∀ request before → Store.lookupCancellation before (Input.token request) ≡ nothing →
    ReplyMeaning request before (canonicalReply (A.original (Input.token request) (Step.registration before)))
  canonicalMeaning request before active with A.original (Input.token request) (Step.registration before) in observed
  ... | inj₁ fault = tt
  ... | inj₂ selectedContext = observed , active

  bindingSignature : Store.BindingRow → Wire.Value
  bindingSignature binding = Wire.array
    (Wire.string (Store.BindingRow.operation binding) ∷ Store.BindingRow.arguments binding ∷ Store.BindingRow.settings binding ∷ [])

  matches : Store.BindingRow → Store.BindingRow → Bool
  matches expected actual = does (Lists.≡-dec Fin._≟_
    (Library.Contract.compactJSON library (bindingSignature expected))
    (Library.Contract.compactJSON library (bindingSignature actual)))

  data Inspection : Set where
    terminal : Result → Inspection
    needsSnapshot : Inspection

  InspectionMeaning : Input → Store.World → Inspection → Set
  InspectionMeaning request before (terminal result) = ReplyMeaning request before result
  InspectionMeaning request before needsSnapshot =
    Store.lookupCancellation before (Input.token request) ≡ nothing × plan (Input.token request) before ≡ nothing

  inspectWith : Input → Store.BindingRow → Store.World → Result → Inspection
  inspectWith request expected before result with AdmissionStore.reservation (Input.token request) (Store.OperationTables.reservations (tables before))
  ... | nothing = terminal (stopped (Step.needsInput unknown))
  ... | just _ with binding (Input.token request) before
  ... | nothing = terminal (stopped (Step.needsInput unknown))
  ... | just actual with matches expected actual
  ... | false = terminal (stopped (Step.needsInput mismatch))
  ... | true with Store.lookupCancellation before (Input.token request)
  ... | just receipt = terminal (stopped (Step.cancelled receipt))
  ... | nothing with plan (Input.token request) before
  ... | nothing = needsSnapshot
  ... | just _ = terminal result

  inspect : Input → Store.BindingRow → Store.World → Inspection
  inspect request expected before = inspectWith request expected before
    (canonicalReply (A.original (Input.token request) (Step.registration before)))

  inspectWithMeaning : ∀ request expected before result →
    (Store.lookupCancellation before (Input.token request) ≡ nothing → ReplyMeaning request before result) →
    InspectionMeaning request before (inspectWith request expected before result)
  inspectWithMeaning request expected before result certified with AdmissionStore.reservation (Input.token request) (Store.OperationTables.reservations (tables before))
  ... | nothing = tt
  ... | just _ with binding (Input.token request) before
  ... | nothing = tt
  ... | just actual with matches expected actual
  ... | false = tt
  ... | true with Store.lookupCancellation before (Input.token request) in cancelled
  ... | just receipt = cancelled
  ... | nothing with plan (Input.token request) before in savedPlan
  ... | nothing = cancelled , savedPlan
  ... | just _ = certified refl

  inspectionMeaning : ∀ request expected before → InspectionMeaning request before (inspect request expected before)
  inspectionMeaning request expected before = inspectWithMeaning request expected before _
    (canonicalMeaning request before)

  checkedInspect : ∀ request expected before → Σ Inspection (InspectionMeaning request before)
  checkedInspect request expected before = inspect request expected before , inspectionMeaning request expected before

  hasSavedRows : ℕ → List Store.SavedReplyRow → Bool
  hasSavedRows token [] = false
  hasSavedRows token (row ∷ rest) = does (token ≟ Store.SavedReplyRow.token row) ∨ hasSavedRows token rest

  hasSaved : ℕ → Store.World → Bool
  hasSaved token before = hasSavedRows token (Store.OperationTables.savedReplies (tables before))

  oldAnswers : Validation.Fault
  oldAnswers = Validation.fault [] Validation.wrongIdentity
    "This token has saved answers but no original plan. Read those answers and ask the user to resolve the older operation; do not select replacement work or invent a result."

-- Progress consumes an actual external observation. A failed read/conversion
-- carries a diagnostic; it never manufactures a valid UUID or source snapshot.
data SnapshotObservation (library : Library.Contract) (format : Encoding.Formatting)
  (observed : Store.World) : Set where
  unavailable : Validation.Fault → SnapshotObservation library format observed
  captured : CaptureEncoding.Encode.Candidate library format (Backfill.capture observed) →
    SnapshotObservation library format observed

record PostgreSQL (library : Library.Contract) (format : Encoding.Formatting) : Set₁ where
  field bindingTimestamp : Input → Store.World → ℤ
        readSnapshot : ∀ before → SnapshotObservation library format before

module Registered (library : Library.Contract) (format : Encoding.Formatting)
  (postgres : PostgreSQL library format) where
  open Preparation library public
  module Codec = CaptureEncoding.Encode library format

  data PlansGrew (request : Input) (selected : List Backfill.Source)
    (original : List Store.PlanRow) : List Store.PlanRow → Set where
    originalPlans : PlansGrew request selected original original
    addedPlan : ∀ current sources (candidate : Codec.Candidate sources) →
      sources ≡ selected → P.plan (Input.token request) current ≡ nothing →
      PlansGrew request selected original current →
      PlansGrew request selected original (Store.planRow (Input.token request) (Codec.rawPlan candidate) ∷ current)

  record Frame (request : Input) (original final : Store.World) : Set where
    field otherFields : protected final ≡ protected original
          bindingRows : BindingsGrew request
            (Store.OperationTables.bindings (tables original)) (Store.OperationTables.bindings (tables final))
          planRows : PlansGrew request (Backfill.capture original)
            (Store.OperationTables.plans (tables original)) (Store.OperationTables.plans (tables final))

  initialFrame : ∀ request original → Frame request original original
  initialFrame request original = record
    { otherFields = refl; bindingRows = originalBindings; planRows = originalPlans }

  frameKeepsCapture : ∀ request original final → Frame request original final → Backfill.capture final ≡ Backfill.capture original
  frameKeepsCapture request original final prior = cong Backfill.capture (Frame.otherFields prior)

  bindKeepsFrame : ∀ request received original before → Frame request original before →
    Frame request original (proj₁ (bind request received before))
  bindKeepsFrame request received original before prior = record
    { otherFields = trans (bindingPreservesProtected request received before) (Frame.otherFields prior)
    ; bindingRows = bindKeepsBindings request received _ before (Frame.bindingRows prior)
    ; planRows = subst (PlansGrew request (Backfill.capture original) (Store.OperationTables.plans (tables original)))
        (sym (bindingKeepsPlans request received before)) (Frame.planRows prior) }

  -- The decision retains its concrete guard/decoder evidence. The retry
  -- laws inspect this decision, not independently reconstructed proof records.
  data Publication (request : Input) (sources : List Backfill.Source)
    (candidate : Codec.Candidate sources) (before : Store.World) : Set where
    preserve : ∀ result → ReplyMeaning request before result → Publication request sources candidate before
    freshPlan : ∀ selectedContext →
      ReplyMeaning request (putPlan (Input.token request) (Codec.rawPlan candidate) before) (ready selectedContext) →
      plan (Input.token request) before ≡ nothing → Publication request sources candidate before

  decidePublication : ∀ request expected sources (candidate : Codec.Candidate sources) before → Publication request sources candidate before
  decidePublication request expected sources candidate before with inspect request expected before | proj₂ (checkedInspect request expected before)
  ... | terminal result | certified = preserve result certified
  ... | needsSnapshot | certified with hasSaved (Input.token request) before
  ... | true = preserve (stopped (Step.needsInput oldAnswers)) tt
  ... | false with A.original (Input.token request) (Step.registration (putPlan (Input.token request) (Codec.rawPlan candidate) before)) in decoded
  ... | inj₁ fault = preserve (stopped (Step.needsInput fault)) tt
  ... | inj₂ selectedContext = freshPlan selectedContext (decoded , proj₁ certified) (proj₂ certified)

  publicationOutcome : ∀ {request sources candidate before} → Publication request sources candidate before → Store.World × Result
  publicationOutcome {before = before} (preserve result certified) = before , result
  publicationOutcome {request} {candidate = candidate} {before} (freshPlan selectedContext certified absent) =
    putPlan (Input.token request) (Codec.rawPlan candidate) before , ready selectedContext

  publicationMeaning : ∀ {request sources candidate before} (chosen : Publication request sources candidate before) →
    ReplyMeaning request (proj₁ (publicationOutcome chosen)) (proj₂ (publicationOutcome chosen))
  publicationMeaning (preserve result certified) = certified
  publicationMeaning (freshPlan selectedContext certified absent) = certified

  publish : ∀ request expected {sources} → Codec.Candidate sources → Store.World → Store.World × Result
  publish request expected {sources} candidate before = publicationOutcome (decidePublication request expected sources candidate before)

  checkedPublish : ∀ request expected sources (candidate : Codec.Candidate sources) before →
    Σ (Store.World × Result) (λ outcome → ReplyMeaning request (proj₁ outcome) (proj₂ outcome))
  checkedPublish request expected sources candidate before = publish request expected candidate before ,
    publicationMeaning (decidePublication request expected sources candidate before)

  publicationKeepsFrame : ∀ request sources (candidate : Codec.Candidate sources) original before →
    sources ≡ Backfill.capture original → Frame request original before →
    (chosen : Publication request sources candidate before) → Frame request original (proj₁ (publicationOutcome chosen))
  publicationKeepsFrame request sources candidate original before represented prior (preserve result certified) = prior
  publicationKeepsFrame request sources candidate original before represented prior (freshPlan selectedContext certified absent) = record
    { otherFields = Frame.otherFields prior
    ; bindingRows = Frame.bindingRows prior
    ; planRows = addedPlan _ sources candidate represented absent (Frame.planRows prior) }

  publishKeepsFrame : ∀ request expected sources (candidate : Codec.Candidate sources) original before →
    sources ≡ Backfill.capture original → Frame request original before → Frame request original (proj₁ (publish request expected candidate before))
  publishKeepsFrame request expected sources candidate original before represented prior =
    publicationKeepsFrame request sources candidate original before represented prior (decidePublication request expected sources candidate before)

  Goal : Input → Store.World → Store.World → Result → Set
  Goal request initial final reply = Frame request initial final × ReplyMeaning request final reply

  boundReceipt : Bound → DB.Receipt
  boundReceipt (bound _) = DB.committed
  boundReceipt (badBinding _) = DB.aborted
  boundReceipt (cancelledBinding _) = DB.aborted

  resultReceipt : Result → DB.Receipt
  resultReceipt (ready _) = DB.committed
  resultReceipt (stopped _) = DB.aborted

  unchangedPhysical : ∀ (before : Store.World) result → DB.Atomic before before (resultReceipt result) before
  unchangedPhysical before (ready _) = DB.committedAll
  unchangedPhysical before (stopped _) = DB.abortedNone

  bindPhysical : ∀ request received before → DB.Atomic before (proj₁ (bind request received before))
    (boundReceipt (proj₂ (bind request received before))) (proj₁ (bind request received before))
  bindPhysical request received before with allowed request before
  ... | false = DB.abortedNone
  ... | true with AdmissionStore.reservation (Input.token request) (Store.OperationTables.reservations (tables before))
  ... | nothing = DB.abortedNone
  ... | just _ with Store.lookupCancellation before (Input.token request)
  ... | just _ = DB.abortedNone
  ... | nothing with binding (Input.token request) before
  ... | just _ = DB.committedAll
  ... | nothing = DB.committedAll

  BoundMeaning : Input → Store.World → Bound → Set
  BoundMeaning request after (bound row) = binding (Input.token request) after ≡ just row
  BoundMeaning request after (badBinding _) = ⊤
  BoundMeaning request after (cancelledBinding receipt) = Store.lookupCancellation after (Input.token request) ≡ just receipt

  bindingMeaning : ∀ request received before → BoundMeaning request
    (proj₁ (bind request received before)) (proj₂ (bind request received before))
  bindingMeaning request received before with allowed request before
  ... | false = tt
  ... | true with AdmissionStore.reservation (Input.token request) (Store.OperationTables.reservations (tables before))
  ... | nothing = tt
  ... | just _ with Store.lookupCancellation before (Input.token request) in cancellation
  ... | just _ = cancellation
  ... | nothing with binding (Input.token request) before in original
  ... | just _ = original
  ... | nothing = headBindingReadable request received before

  publishPhysical : ∀ request expected sources (candidate : Codec.Candidate sources) before →
    DB.Atomic before (proj₁ (publish request expected candidate before))
      (resultReceipt (proj₂ (publish request expected candidate before))) (proj₁ (publish request expected candidate before))
  publishPhysical request expected sources candidate before with decidePublication request expected sources candidate before
  ... | preserve result certified = unchangedPhysical before result
  ... | freshPlan selectedContext certified absent = DB.committedAll

  data Effect : Set where
    bindOriginal : Input → Effect
    inspectOriginal : Input → Store.BindingRow → Effect
    readSnapshot : Effect
    publishOriginal : (request : Input) → Store.BindingRow → ∀ {sources} → Codec.Candidate sources → Effect

  Reply : Effect → Set
  Reply (bindOriginal request) = ℤ × Bound
  Reply (inspectOriginal request expected) = Inspection
  Reply readSnapshot = Σ Store.World (SnapshotObservation library format)
  Reply (publishOriginal request expected candidate) = Result

  Atomic : Store.World → (effect : Effect) → Reply effect → Store.World → Set
  Atomic before (bindOriginal request) (received , reply) after =
    reply ≡ proj₂ (bind request received before) ×
    DB.Atomic before (proj₁ (bind request received before)) (boundReceipt reply) after
  Atomic before (inspectOriginal request expected) reply after =
    reply ≡ inspect request expected before × after ≡ before
  Atomic before readSnapshot (observed , packet) after = observed ≡ before × after ≡ before
  Atomic before (publishOriginal request expected candidate) reply after =
    reply ≡ proj₂ (publish request expected candidate before) ×
    DB.Atomic before (proj₁ (publish request expected candidate before)) (resultReceipt reply) after

  module X = Recovery.Execution Store.World Effect Reply Atomic
  module E = X.E

  afterSnapshot : ∀ request expected → Reply readSnapshot → E.Script Result
  afterSnapshot request expected (observed , unavailable fault) = E.done (stopped (Step.needsInput fault))
  afterSnapshot request expected (observed , captured candidate) = E.ask (publishOriginal request expected candidate) E.done

  afterInspection : ∀ request expected → Inspection → E.Script Result
  afterInspection request expected (terminal result) = E.done result
  afterInspection request expected needsSnapshot = E.ask readSnapshot (afterSnapshot request expected)

  afterBinding : ∀ request → Reply (bindOriginal request) → E.Script Result
  afterBinding request (received , bound original) = E.ask (inspectOriginal request original) (afterInspection request original)
  afterBinding request (received , badBinding fault) = E.done (stopped (Step.needsInput fault))
  afterBinding request (received , cancelledBinding receipt) = E.done (stopped (Step.cancelled receipt))

  script : Input → E.Script Result
  script request = E.ask (bindOriginal request) (afterBinding request)

  knownBoundUnique : ∀ {before proposed first second : Store.World} (reply : Bound) →
    DB.Atomic before proposed (boundReceipt reply) first → DB.Atomic before proposed (boundReceipt reply) second → first ≡ second
  knownBoundUnique (bound _) DB.committedAll DB.committedAll = refl
  knownBoundUnique (badBinding _) DB.abortedNone DB.abortedNone = refl
  knownBoundUnique (cancelledBinding _) DB.abortedNone DB.abortedNone = refl

  knownResultUnique : ∀ {before proposed first second : Store.World} (reply : Result) →
    DB.Atomic before proposed (resultReceipt reply) first → DB.Atomic before proposed (resultReceipt reply) second → first ≡ second
  knownResultUnique (ready _) DB.committedAll DB.committedAll = refl
  knownResultUnique (stopped _) DB.abortedNone DB.abortedNone = refl

  bindingObservation : ∀ request received before after reply → Atomic before (bindOriginal request) (received , reply) after →
    (after , reply) ≡ bind request received before
  bindingObservation request received before after .(proj₂ (bind request received before)) (refl , physical) =
    cong (λ current → current , proj₂ (bind request received before))
      (knownBoundUnique (proj₂ (bind request received before)) physical (bindPhysical request received before))

  publicationObservation : ∀ request expected sources (candidate : Codec.Candidate sources) before after reply →
    Atomic before (publishOriginal request expected candidate) reply after →
    (after , reply) ≡ publish request expected candidate before
  publicationObservation request expected sources candidate before after .(proj₂ (publish request expected candidate before)) (refl , physical) =
    cong (λ current → current , proj₂ (publish request expected candidate before))
      (knownResultUnique (proj₂ (publish request expected candidate before)) physical (publishPhysical request expected sources candidate before))

  -- The checked continuation carries the concrete business/ownership meaning
  -- at EVERY reachable state, including a statement whose reply was lost.
  data Safe (request : Input) (initial : Store.World) : E.Script Result → Store.World → Set where
    returned : ∀ before reply → Goal request initial before reply → Safe request initial (E.done reply) before
    awaiting : ∀ before effect next → Frame request initial before →
      (∀ reply after → Atomic before effect reply after → Safe request initial (next reply) after) →
      Safe request initial (E.ask effect next) before

  safeFrame : ∀ {request initial program before} → Safe request initial program before → Frame request initial before
  safeFrame (returned before reply goal) = proj₁ goal
  safeFrame (awaiting before effect next prior continuation) = prior

  safeRuns : ∀ {request initial program before events after reply} → Safe request initial program before →
    E.Runs program events reply → X.Changes before events after → Goal request initial after reply
  safeRuns (returned before reply goal) (E.returned _) (X.unchanged _) = goal
  safeRuns (awaiting before effect next prior continuation) (E.replied _ _ reply rest)
    (X.changed _ _ _ middle physical changes) = safeRuns (continuation reply middle physical) rest changes

  safeCompleted : ∀ {request initial program before after reply} → Safe request initial program before →
    X.Completed program before after reply → Goal request initial after reply
  safeCompleted checked (X.completed events execution changes) = safeRuns checked execution changes

  safePrefix : ∀ {request initial program before events residual current} → Safe request initial program before →
    E.Prefix program events residual → X.Changes before events current → Safe request initial residual current
  safePrefix checked (E.stopped _) (X.unchanged _) = checked
  safePrefix (awaiting before effect next prior continuation) (E.replied _ _ reply rest)
    (X.changed _ _ _ middle physical changes) = safePrefix (continuation reply middle physical) rest changes

  safeInterrupted : ∀ {request initial program before current} → Safe request initial program before →
    X.Interrupted program before current → Frame request initial current
  safeInterrupted checked (X.atPrefix events residual current prefix changes) = safeFrame (safePrefix checked prefix changes)
  safeInterrupted checked (X.beforeReply events effect next current reply after prefix changes physical)
    with safePrefix checked prefix changes
  ... | awaiting _ _ _ prior continuation = safeFrame (continuation reply after physical)

  safePublication : ∀ request expected sources (candidate : Codec.Candidate sources) initial before →
    sources ≡ Backfill.capture initial → Frame request initial before →
    Safe request initial (E.ask (publishOriginal request expected candidate) E.done) before
  safePublication request expected sources candidate initial before represented prior = awaiting before
    (publishOriginal request expected candidate) E.done prior λ reply after physical →
      returned after reply (subst (λ outcome → Goal request initial (proj₁ outcome) (proj₂ outcome))
        (sym (publicationObservation request expected sources candidate before after reply physical))
        (publishKeepsFrame request expected sources candidate initial before represented prior ,
          proj₂ (checkedPublish request expected sources candidate before)))

  safeSnapshot : ∀ request expected initial before → Frame request initial before →
    Safe request initial (E.ask readSnapshot (afterSnapshot request expected)) before
  safeSnapshot request expected initial before prior = awaiting before readSnapshot (afterSnapshot request expected) prior next
    where
    next : ∀ observed after → Atomic before readSnapshot observed after →
      Safe request initial (afterSnapshot request expected observed) after
    next (observed , unavailable fault) .before (refl , refl) = returned before (stopped (Step.needsInput fault)) (prior , tt)
    next (observed , captured candidate) .before (refl , refl) =
      safePublication request expected _ candidate initial before (frameKeepsCapture request initial before prior) prior

  safeInspectionContinuation : ∀ request expected initial before inspection → Frame request initial before →
    InspectionMeaning request before inspection → Safe request initial (afterInspection request expected inspection) before
  safeInspectionContinuation request expected initial before (terminal result) prior certified = returned before result (prior , certified)
  safeInspectionContinuation request expected initial before needsSnapshot prior certified = safeSnapshot request expected initial before prior

  safeInspection : ∀ request expected initial before → Frame request initial before →
    Safe request initial (E.ask (inspectOriginal request expected) (afterInspection request expected)) before
  safeInspection request expected initial before prior = awaiting before
    (inspectOriginal request expected) (afterInspection request expected) prior next
    where
    next : ∀ reply after → Atomic before (inspectOriginal request expected) reply after →
      Safe request initial (afterInspection request expected reply) after
    next .(inspect request expected before) .before (refl , refl) =
      safeInspectionContinuation request expected initial before (inspect request expected before) prior
        (proj₂ (checkedInspect request expected before))

  safeBindingContinuation : ∀ request received initial before reply → Frame request initial before → BoundMeaning request before reply →
    Safe request initial (afterBinding request (received , reply)) before
  safeBindingContinuation request received initial before (bound original) prior certified = safeInspection request original initial before prior
  safeBindingContinuation request received initial before (badBinding fault) prior certified = returned before (stopped (Step.needsInput fault)) (prior , tt)
  safeBindingContinuation request received initial before (cancelledBinding receipt) prior certified = returned before (stopped (Step.cancelled receipt)) (prior , certified)

  safeScript : ∀ request initial before → Frame request initial before → Safe request initial (script request) before
  safeScript request initial before prior = awaiting before (bindOriginal request) (afterBinding request) prior next
    where
    next : ∀ reply after → Atomic before (bindOriginal request) reply after →
      Safe request initial (afterBinding request reply) after
    next (received , reply) after physical = subst
      (λ outcome → Safe request initial (afterBinding request (received , proj₂ outcome)) (proj₁ outcome))
      (sym (bindingObservation request received before after reply physical))
      (safeBindingContinuation request received initial (proj₁ (bind request received before)) (proj₂ (bind request received before))
        (bindKeepsFrame request received initial before prior) (bindingMeaning request received before))

  converges : ∀ request initial interrupted final reply → X.Interrupted (script request) initial interrupted →
    X.Completed (script request) interrupted final reply → Goal request initial final reply
  converges request initial interrupted final reply interruption completion = safeCompleted
    (safeScript request initial interrupted (safeInterrupted (safeScript request initial initial (initialFrame request initial)) interruption)) completion

  prepend : ∀ effect next before response middle → Atomic before effect response middle →
    Σ Store.World (λ after → Σ Result (λ reply → X.Completed (next response) middle after reply)) →
    Σ Store.World (λ after → Σ Result (λ reply → X.Completed (E.ask effect next) before after reply))
  prepend effect next before response middle physical (after , reply , X.completed events execution changes) =
    after , reply , X.completed ((effect , response) ∷ events) (E.replied effect next response execution)
      (X.changed before effect response middle physical changes)

  finished : ∀ before reply → Σ Store.World (λ after → Σ Result (λ result → X.Completed (E.done reply) before after result))
  finished before reply = before , reply , X.completed [] (E.returned reply) (X.unchanged before)

  progressPublication : ∀ request expected sources (candidate : Codec.Candidate sources) before →
    Σ Store.World (λ after → Σ Result (λ reply → X.Completed (E.ask (publishOriginal request expected candidate) E.done) before after reply))
  progressPublication request expected sources candidate before =
    prepend (publishOriginal request expected candidate) E.done before
      (proj₂ (publish request expected candidate before)) (proj₁ (publish request expected candidate before))
      (refl , publishPhysical request expected sources candidate before)
      (finished (proj₁ (publish request expected candidate before)) (proj₂ (publish request expected candidate before)))

  progressAfterSnapshot : ∀ request expected observation before →
    Σ Store.World (λ after → Σ Result (λ reply → X.Completed (afterSnapshot request expected observation) before after reply))
  progressAfterSnapshot request expected (observed , unavailable fault) before = finished before (stopped (Step.needsInput fault))
  progressAfterSnapshot request expected (observed , captured candidate) before = progressPublication request expected _ candidate before

  progressSnapshot : ∀ request expected before →
    Σ Store.World (λ after → Σ Result (λ reply → X.Completed (E.ask readSnapshot (afterSnapshot request expected)) before after reply))
  progressSnapshot request expected before = prepend readSnapshot (afterSnapshot request expected) before
    (before , PostgreSQL.readSnapshot postgres before) before (refl , refl)
    (progressAfterSnapshot request expected (before , PostgreSQL.readSnapshot postgres before) before)

  progressAfterInspection : ∀ request expected inspection before →
    Σ Store.World (λ after → Σ Result (λ reply → X.Completed (afterInspection request expected inspection) before after reply))
  progressAfterInspection request expected (terminal result) before = finished before result
  progressAfterInspection request expected needsSnapshot before = progressSnapshot request expected before

  progressInspection : ∀ request expected before →
    Σ Store.World (λ after → Σ Result (λ reply → X.Completed (E.ask (inspectOriginal request expected) (afterInspection request expected)) before after reply))
  progressInspection request expected before = prepend (inspectOriginal request expected) (afterInspection request expected) before
    (inspect request expected before) before (refl , refl) (progressAfterInspection request expected (inspect request expected before) before)

  progressAfterBinding : ∀ request observation before →
    Σ Store.World (λ after → Σ Result (λ reply → X.Completed (afterBinding request observation) before after reply))
  progressAfterBinding request (received , bound original) before = progressInspection request original before
  progressAfterBinding request (received , badBinding fault) before = finished before (stopped (Step.needsInput fault))
  progressAfterBinding request (received , cancelledBinding receipt) before = finished before (stopped (Step.cancelled receipt))

  progress : ∀ request before → Σ Store.World (λ after → Σ Result (λ reply → X.Completed (script request) before after reply))
  progress request before = prepend (bindOriginal request) (afterBinding request) before
    (received , proj₂ (bind request received before)) (proj₁ (bind request received before))
    (refl , bindPhysical request received before)
    (progressAfterBinding request (received , proj₂ (bind request received before)) (proj₁ (bind request received before)))
    where received = PostgreSQL.bindingTimestamp postgres request before

  operation : Recovery.RecoverableFor Store.World Input Result Goal
  operation = record
    { Effect = Effect; Reply = Reply; script = script; Atomic = Atomic; converges = converges; progress = progress }

  record Existing (request : Input) (before : Store.World) : Set where
    field reserved : Store.ReservationRow
          original : Store.BindingRow
          raw : Wire.Value
          reservationPresent : AdmissionStore.reservation (Input.token request) (Store.OperationTables.reservations (tables before)) ≡ just reserved
          bindingPresent : binding (Input.token request) before ≡ just original
          planPresent : plan (Input.token request) before ≡ just raw
          isReembed : Controls.Plan.textEqual (Store.BindingRow.operation original) (toList "reembed") ≡ true
          arguments : Store.BindingRow.arguments original ≡ Wire.object []
          configured : A.provider (Store.BindingRow.settings original) ≡ true

  registeredFacts : ∀ request before reserved original raw →
    AdmissionStore.originalPlan (toList "reembed") (Input.token request) (Step.registration before) ≡ inj₂ (reserved , original , raw) →
    Store.BindingRow.arguments original ≡ Wire.object [] → A.provider (Store.BindingRow.settings original) ≡ true → Existing request before
  registeredFacts request before reserved original raw known arguments configured
    with AdmissionStore.reservation (Input.token request) (Store.OperationTables.reservations (tables before)) in reservationFound
  ... | nothing with known
  ... | ()
  registeredFacts request before reserved original raw known arguments configured | just actualReservation
    with binding (Input.token request) before in bindingFound
  ... | nothing with known
  ... | ()
  registeredFacts request before reserved original raw known arguments configured | just actualReservation | just actualBinding
    with Controls.Plan.textEqual (Store.BindingRow.operation actualBinding) (toList "reembed") in operationFound
  ... | false with known
  ... | ()
  registeredFacts request before reserved original raw known arguments configured | just actualReservation | just actualBinding | true
    with plan (Input.token request) before in planFound
  ... | nothing with known
  ... | ()
  registeredFacts request before reserved original raw known arguments configured | just actualReservation | just actualBinding | true | just actualPlan with known
  ... | refl = record
    { reserved = actualReservation; original = actualBinding; raw = actualPlan
    ; reservationPresent = reservationFound; bindingPresent = bindingFound; planPresent = planFound
    ; isReembed = operationFound; arguments = arguments; configured = configured }

  canonicalFacts : ∀ request before selectedContext → A.original (Input.token request) (Step.registration before) ≡ inj₂ selectedContext → Existing request before
  canonicalFacts request before selectedContext known
    with AdmissionStore.originalPlan (toList "reembed") (Input.token request) (Step.registration before) in resolved
  ... | inj₁ fault with known
  ... | ()
  canonicalFacts request before selectedContext known | inj₂ (reserved , original , raw)
    with Store.BindingRow.arguments original in arguments | A.provider (Store.BindingRow.settings original) in configured
  ... | Wire.object [] | true = registeredFacts request before reserved original raw resolved arguments configured
  canonicalFacts request before selectedContext known | inj₂ (reserved , original , raw) | Wire.object [] | false with known
  ... | ()
  canonicalFacts request before selectedContext known | inj₂ (reserved , original , raw) | Wire.object (_ ∷ _) | _ with known
  ... | ()
  canonicalFacts request before selectedContext known | inj₂ (reserved , original , raw) | Wire.null | _ with known
  ... | ()
  canonicalFacts request before selectedContext known | inj₂ (reserved , original , raw) | Wire.boolean _ | _ with known
  ... | ()
  canonicalFacts request before selectedContext known | inj₂ (reserved , original , raw) | Wire.string _ | _ with known
  ... | ()
  canonicalFacts request before selectedContext known | inj₂ (reserved , original , raw) | Wire.signed _ | _ with known
  ... | ()
  canonicalFacts request before selectedContext known | inj₂ (reserved , original , raw) | Wire.unsigned _ | _ with known
  ... | ()
  canonicalFacts request before selectedContext known | inj₂ (reserved , original , raw) | Wire.floating _ | _ with known
  ... | ()
  canonicalFacts request before selectedContext known | inj₂ (reserved , original , raw) | Wire.array _ | _ with known
  ... | ()

  existingAllowed : ∀ request before → Existing request before → allowed request before ≡ true
  existingAllowed request before existing rewrite Existing.bindingPresent existing | Existing.isReembed existing
    | Existing.arguments existing | Existing.configured existing = refl

  bindingReplay : ∀ request received before (existing : Existing request before) →
    Store.lookupCancellation before (Input.token request) ≡ nothing →
    bind request received before ≡ (before , bound (Existing.original existing))
  bindingReplay request received before existing active rewrite existingAllowed request before existing
    | Existing.reservationPresent existing | active | Existing.bindingPresent existing = refl

  matchesSelf : ∀ original → matches original original ≡ true
  matchesSelf original with Lists.≡-dec Fin._≟_
    (Library.Contract.compactJSON library (bindingSignature original))
    (Library.Contract.compactJSON library (bindingSignature original))
  ... | yes _ = refl
  ... | no impossible = ⊥-elim (impossible refl)

  inspectionReplay : ∀ request before selectedContext (existing : Existing request before) →
    A.original (Input.token request) (Step.registration before) ≡ inj₂ selectedContext →
    Store.lookupCancellation before (Input.token request) ≡ nothing →
    inspect request (Existing.original existing) before ≡ terminal (ready selectedContext)
  inspectionReplay request before selectedContext existing known active
    rewrite known | Existing.reservationPresent existing | Existing.bindingPresent existing
      | matchesSelf (Existing.original existing) | active | Existing.planPresent existing = refl

  doneObservation : ∀ (before after : Store.World) (expected reply : Result) events → E.Runs (E.done expected) events reply →
    X.Changes before events after → after ≡ before × reply ≡ expected
  doneObservation before .before expected .expected .[] (E.returned _) (X.unchanged _) = refl , refl

  inspectionCompletion : ∀ request expected before after selectedContext reply →
    inspect request expected before ≡ terminal (ready selectedContext) →
    X.Completed (E.ask (inspectOriginal request expected) (afterInspection request expected)) before after reply →
    after ≡ before × reply ≡ ready selectedContext
  inspectionCompletion request expected before after selectedContext reply known
    (X.completed (_ ∷ events) (E.replied _ _ observed execution)
      (X.changed _ _ _ middle (reported , unchanged) changes))
    with doneObservation middle after (ready selectedContext) reply events
      (subst (λ reading → E.Runs (afterInspection request expected reading) events reply) (trans reported known) execution) changes
  ... | state , answer = trans state unchanged , answer

  -- Once the original plan exists, replay performs no capture/provider work.
  -- It returns that same decoder-derived capability regardless of current
  -- configuration and independently observed PostgreSQL timestamps.
  replayReady : ∀ request before selectedContext {middle prepared} →
    A.original (Input.token request) (Step.registration before) ≡ inj₂ selectedContext →
    Store.lookupCancellation before (Input.token request) ≡ nothing →
    X.Completed (script request) before middle prepared →
    middle ≡ before × prepared ≡ ready selectedContext
  replayReady request before selectedContext {middle = final} {prepared} known active
    (X.completed (_ ∷ events) (E.replied _ _ (received , reply) execution)
      (X.changed _ _ _ middle physical changes)) = trans (proj₁ remaining) state , proj₂ remaining
    where
    existing = canonicalFacts request before selectedContext known
    observed = trans (bindingObservation request received before middle reply physical)
      (bindingReplay request received before existing active)
    state = cong proj₁ observed
    reported = cong proj₂ observed
    subsequent = X.completed events
      (subst (λ result → E.Runs (afterBinding request (received , result)) events prepared) reported execution) changes
    inspected = trans (cong (inspect request (Existing.original existing)) state)
      (inspectionReplay request before selectedContext existing known active)
    remaining = inspectionCompletion request (Existing.original existing) middle final selectedContext prepared inspected subsequent

  completedReadyCanonical : ∀ request before after selectedContext → X.Completed (script request) before after (ready selectedContext) →
    A.original (Input.token request) (Step.registration after) ≡ inj₂ selectedContext
  completedReadyCanonical request before after selectedContext completion = proj₁ (proj₂
    (Recovery.RecoverableFor.completedMeetsGoal operation request before after (ready selectedContext) completion))

  completedReadyNotCancelled : ∀ request before after selectedContext → X.Completed (script request) before after (ready selectedContext) →
    Store.lookupCancellation after (Input.token request) ≡ nothing
  completedReadyNotCancelled request before after selectedContext completion = proj₂ (proj₂
    (Recovery.RecoverableFor.completedMeetsGoal operation request before after (ready selectedContext) completion))

  existingPlanCannotBeReplaced : ∀ request expected sources (candidate : Codec.Candidate sources) before original →
    plan (Input.token request) before ≡ just original → proj₁ (publish request expected candidate before) ≡ before
  existingPlanCannotBeReplaced request expected sources candidate before original known
    with decidePublication request expected sources candidate before
  ... | preserve result certified = refl
  ... | freshPlan selectedContext certified absent with trans (sym known) absent
  ... | ()

  everyBindingReceiptCovered : ∀ request received before receipt after →
    DB.Atomic before (proj₁ (bind request received before)) receipt after → X.Interrupted (script request) before after
  everyBindingReceiptCovered request received before .DB.committed .(proj₁ (bind request received before)) DB.committedAll =
    X.beforeReply [] (bindOriginal request) (afterBinding request) before
      (received , proj₂ (bind request received before)) _ (E.stopped _) (X.unchanged before)
      (refl , bindPhysical request received before)
  everyBindingReceiptCovered request received before .DB.aborted .before DB.abortedNone =
    X.atPrefix [] (script request) before (E.stopped _) (X.unchanged before)
  everyBindingReceiptCovered request received before .DB.acknowledgementLost .before DB.unknownBefore =
    X.atPrefix [] (script request) before (E.stopped _) (X.unchanged before)
  everyBindingReceiptCovered request received before .DB.acknowledgementLost .(proj₁ (bind request received before)) DB.unknownAfter =
    X.beforeReply [] (bindOriginal request) (afterBinding request) before
      (received , proj₂ (bind request received before)) _ (E.stopped _) (X.unchanged before)
      (refl , bindPhysical request received before)

  everyPlanReceiptCovered : ∀ request expected sources (candidate : Codec.Candidate sources) before receipt after →
    DB.Atomic before (proj₁ (publish request expected candidate before)) receipt after →
    X.Interrupted (E.ask (publishOriginal request expected candidate) E.done) before after
  everyPlanReceiptCovered request expected sources candidate before .DB.committed .(proj₁ (publish request expected candidate before)) DB.committedAll =
    X.beforeReply [] (publishOriginal request expected candidate) E.done before
      (proj₂ (publish request expected candidate before)) _ (E.stopped _) (X.unchanged before)
      (refl , publishPhysical request expected sources candidate before)
  everyPlanReceiptCovered request expected sources candidate before .DB.aborted .before DB.abortedNone =
    X.atPrefix [] (E.ask (publishOriginal request expected candidate) E.done) before (E.stopped _) (X.unchanged before)
  everyPlanReceiptCovered request expected sources candidate before .DB.acknowledgementLost .before DB.unknownBefore =
    X.atPrefix [] (E.ask (publishOriginal request expected candidate) E.done) before (E.stopped _) (X.unchanged before)
  everyPlanReceiptCovered request expected sources candidate before .DB.acknowledgementLost .(proj₁ (publish request expected candidate before)) DB.unknownAfter =
    X.beforeReply [] (publishOriginal request expected candidate) E.done before
      (proj₂ (publish request expected candidate before)) _ (E.stopped _) (X.unchanged before)
      (refl , publishPhysical request expected sources candidate before)
