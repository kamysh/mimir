{-# OPTIONS --safe #-}
-- Concrete operation controls. Request identities are admitted inputs;
-- PostgreSQL-generated metadata belongs to physical replies, never requests.
module Mimir.OperationControls where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_; _++_; map; filterᵇ; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_; _<?_; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String using (String; toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Relation.Nullary using (¬_; yes; no; does)
open import Mimir.Text using (Text; Nonblank)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.ApplicationStore as Store
import Mimir.DatabaseTransaction as DB
import Mimir.Recovery as Recovery
import Mimir.RegisteredStoreAdmission as Admission
import Mimir.StructuredValue as Wire
import Mimir.StandardLibrary as Library
import Mimir.RecordDecoding as Decode
import Mimir.JsonObjects as Objects
import Mimir.Validation as Validation
import Mimir.CharacterRules as Characters
import Mimir.Text as Text
import Mimir.ProjectDeletion as Project
import Mimir.RecoverableStoreStep as StoreStep
import Mimir.PublicInput as PublicInput

record RequestKey : Set where
  constructor requestKey
  field text : Text; admitted : Nonblank text

admitRequestKey : Text → Validation.Fault ⊎ RequestKey
admitRequestKey raw with Text.nonblank? raw
... | yes valid = inj₂ (requestKey raw valid)
... | no invalid = inj₁ (Validation.fault (Validation.key "request_key" ∷ []) Validation.malformedInput
  "Supply a nonblank stable request_key for this action. Reuse that exact key after a lost reply; ask the user if the intended action is unknown.")

lookupKey : Text → List Store.RequestKeyRow → Maybe ℕ
lookupKey key [] = nothing
lookupKey key (row ∷ rest) with key ≟Text Store.RequestKeyRow.requestKey row
... | yes _ = just (Store.RequestKeyRow.token row)
... | no _ = lookupKey key rest

reservation : ℕ → Store.World → Maybe Store.ReservationRow
reservation token state = Admission.reservation token (Store.OperationTables.reservations (Store.World.operations state))

-- This is a successful DEFAULT VALUES RETURNING receipt and its existing
-- primary-key guarantee, not a theorem that random UUIDs never collide.
-- An adapter supplies this external capability; no instance is fabricated here.
record DefaultReturning (before : Store.World) : Set where
  constructor defaultReturning
  field row : Store.ReservationRow
        unused : reservation (Store.ReservationRow.token row) before ≡ nothing

record PostgreSQL : Set₁ where
  field reservationDefault : ∀ before → DefaultReturning before
        cancellationTimestamp : ℕ → Store.World → ℤ
        storedStepBefore : Text → Text → Bool -- actual database ORDER BY step

-- Both mutating controls have one committed publication with metadata selected
-- by its observed database reply. Goal is fixed by concrete control assembly.
private
  module ReceiptStep (Input Metadata Result : Set)
    (execute : Input → Metadata → Store.World → Store.World × Result)
    (Received : Input → Metadata → Store.World → Set)
    (available : ∀ input before → Σ Metadata (λ metadata → Received input metadata before))
    (stable : ∀ input first second before →
      execute input second (proj₁ (execute input first before)) ≡ execute input first before)
    (Goal : Input → Store.World → Store.World → Result → Set)
    (meaning : ∀ input metadata before → Received input metadata before →
      Goal input before (proj₁ (execute input metadata before)) (proj₂ (execute input metadata before))) where

    Reply : Input → Set
    Reply _ = Metadata × Result

    Atomic : Store.World → (input : Input) → Reply input → Store.World → Set
    Atomic before input (metadata , reply) after =
      Received input metadata before ×
      (reply ≡ proj₂ (execute input metadata before) ×
       DB.Atomic before (proj₁ (execute input metadata before)) DB.committed after)

    module X = Recovery.Execution Store.World Input Reply Atomic
    module E = X.E

    script : Input → E.Script Result
    script input = E.ask input (λ observed → E.done (proj₂ observed))

    atomicObservation : ∀ input metadata before after reply →
      Atomic before input (metadata , reply) after →
      (after , reply) ≡ execute input metadata before
    atomicObservation input metadata before .(proj₁ (execute input metadata before))
      .(proj₂ (execute input metadata before)) (receipt , refl , DB.committedAll) = refl

    completedObservation : ∀ input before after reply →
      X.Completed (script input) before after reply →
      Σ Metadata (λ metadata → Received input metadata before ×
        (after , reply) ≡ execute input metadata before)
    completedObservation input before after reply
      (X.completed _ (E.replied _ _ (metadata , .reply) (E.returned _))
        (X.changed _ _ _ _ physical (X.unchanged _))) =
      metadata , proj₁ physical , atomicObservation input metadata before after reply physical

    interruptionState : ∀ input before interrupted →
      X.Interrupted (script input) before interrupted →
      interrupted ≡ before ⊎ Σ Metadata (λ metadata →
        Received input metadata before × interrupted ≡ proj₁ (execute input metadata before))
    interruptionState input before interrupted (X.atPrefix _ _ _ (E.stopped _) (X.unchanged _)) = inj₁ refl
    interruptionState input before interrupted
      (X.atPrefix _ _ _ (E.replied _ _ (metadata , reply) (E.stopped _))
        (X.changed _ _ _ _ physical (X.unchanged _))) =
      inj₂ (metadata , proj₁ physical , cong proj₁ (atomicObservation input metadata before interrupted reply physical))
    interruptionState input before interrupted
      (X.beforeReply _ _ _ _ (metadata , reply) _ (E.stopped _) (X.unchanged _) physical) =
      inj₂ (metadata , proj₁ physical , cong proj₁ (atomicObservation input metadata before interrupted reply physical))
    interruptionState input before interrupted (X.beforeReply _ _ _ _ _ _ (E.replied _ _ _ ()) changes physical)

    fromObservation : ∀ input metadata before after reply → Received input metadata before →
      (after , reply) ≡ execute input metadata before → Goal input before after reply
    fromObservation input metadata before after reply received observed = subst
      (λ result → Goal input before (proj₁ result) (proj₂ result)) (sym observed)
      (meaning input metadata before received)

    converges : ∀ input before interrupted after reply →
      X.Interrupted (script input) before interrupted → X.Completed (script input) interrupted after reply →
      Goal input before after reply
    converges input before interrupted after reply interruption completion
      with interruptionState input before interrupted interruption | completedObservation input interrupted after reply completion
    ... | inj₁ same | metadata , received , observed =
      fromObservation input metadata before after reply
        (subst (Received input metadata) same received)
        (trans observed (cong (execute input metadata) same))
    ... | inj₂ (first , received , same) | second , later , observed =
      fromObservation input first before after reply received
        (trans observed (trans (cong (execute input second) same) (stable input first second before)))

    progress : ∀ input before → Σ Store.World (λ after → Σ Result (λ reply → X.Completed (script input) before after reply))
    progress input before with available input before
    ... | metadata , received = proj₁ expected , proj₂ expected , X.completed
      ((input , metadata , proj₂ expected) ∷ [])
      (E.replied input (λ reply → E.done (proj₂ reply)) (metadata , proj₂ expected) (E.returned _))
      (X.changed before input _ _ (received , refl , DB.committedAll) (X.unchanged _))
      where expected = execute input metadata before

    everyDatabaseReceiptCovered : ∀ input metadata before → Received input metadata before →
      ∀ tag actual → DB.Atomic before (proj₁ (execute input metadata before)) tag actual →
      X.Interrupted (script input) before actual
    everyDatabaseReceiptCovered input metadata before received .DB.committed _ DB.committedAll =
      X.beforeReply [] input (λ reply → E.done (proj₂ reply)) before
        (metadata , proj₂ (execute input metadata before)) _
        (E.stopped _) (X.unchanged before) (received , refl , DB.committedAll)
    everyDatabaseReceiptCovered input metadata before received .DB.aborted _ DB.abortedNone =
      X.atPrefix [] (script input) before (E.stopped _) (X.unchanged before)
    everyDatabaseReceiptCovered input metadata before received .DB.acknowledgementLost _ DB.unknownBefore =
      X.atPrefix [] (script input) before (E.stopped _) (X.unchanged before)
    everyDatabaseReceiptCovered input metadata before received .DB.acknowledgementLost _ DB.unknownAfter =
      X.beforeReply [] input (λ reply → E.done (proj₂ reply)) before
        (metadata , proj₂ (execute input metadata before)) _
        (E.stopped _) (X.unchanged before) (received , refl , DB.committedAll)

    operation : Recovery.RecoverableFor Store.World Input Result Goal
    operation = record
      { Effect = Input; Reply = Reply; script = script; Atomic = Atomic
      ; converges = converges; progress = progress }

module Reservation (postgres : PostgreSQL) where
  data Existing : Set where
    vacant : Existing
    original : Store.ReservationRow → Existing
    broken : ℕ → Existing

  inspect : RequestKey → Store.World → Existing
  inspect key before with lookupKey (RequestKey.text key) (Store.OperationTables.requestKeys (Store.World.operations before))
  ... | nothing = vacant
  ... | just token with reservation token before
  ... | just row = original row
  ... | nothing = broken token

  data Result : Set where
    reserved : Store.ReservationRow → Result
    needsRecovery : ℕ → Result

  publish : RequestKey → Store.ReservationRow → Store.World → Store.World
  publish key row before = record before { operations = record tables
    { reservations = row ∷ Store.OperationTables.reservations tables
    ; requestKeys = Store.requestKeyRow (RequestKey.text key) (Store.ReservationRow.token row) ∷ Store.OperationTables.requestKeys tables } }
    where tables = Store.World.operations before

  execute : RequestKey → Store.ReservationRow → Store.World → Store.World × Result
  execute key row before with inspect key before
  ... | vacant = publish key row before , reserved row
  ... | original saved = before , reserved saved
  ... | broken token = before , needsRecovery token

  publishedReadable : ∀ key row before → inspect key (publish key row before) ≡ original row
  publishedReadable key row before with RequestKey.text key ≟Text RequestKey.text key
  ... | no impossible = ⊥-elim (impossible refl)
  ... | yes _ with Store.ReservationRow.token row ≟ Store.ReservationRow.token row
  ... | no impossible = ⊥-elim (impossible refl)
  ... | yes _ = refl

  stable : ∀ key first second before → execute key second (proj₁ (execute key first before)) ≡ execute key first before
  stable key first second before with inspect key before in observed
  ... | vacant rewrite publishedReadable key first before = refl
  ... | original saved rewrite observed = refl
  ... | broken token rewrite observed = refl

  Received : RequestKey → Store.ReservationRow → Store.World → Set
  Received key row before with inspect key before
  ... | vacant = reservation (Store.ReservationRow.token row) before ≡ nothing
  ... | original saved = row ≡ saved
  ... | broken token = ⊤

  available : ∀ key before → Σ Store.ReservationRow (λ row → Received key row before)
  available key before with inspect key before
  ... | vacant = DefaultReturning.row observed , DefaultReturning.unused observed
    where observed = PostgreSQL.reservationDefault postgres before
  ... | original saved = saved , refl
  ... | broken token = DefaultReturning.row (PostgreSQL.reservationDefault postgres before) , tt

  Goal : RequestKey → Store.World → Store.World → Result → Set
  Goal key before after reply with inspect key before
  ... | vacant = Σ Store.ReservationRow (λ row →
      reservation (Store.ReservationRow.token row) before ≡ nothing ×
      (after ≡ publish key row before × reply ≡ reserved row))
  ... | original saved = after ≡ before × reply ≡ reserved saved
  ... | broken token = after ≡ before × reply ≡ needsRecovery token

  meaning : ∀ key row before → Received key row before →
    Goal key before (proj₁ (execute key row before)) (proj₂ (execute key row before))
  meaning key row before received with inspect key before
  ... | vacant = row , received , refl , refl
  ... | original saved = refl , refl
  ... | broken token = refl , refl

  module Observed = ReceiptStep RequestKey Store.ReservationRow Result execute Received available stable Goal meaning
  operation = Observed.operation

  Success : Result → Set
  Success (reserved _) = ⊤
  Success (needsRecovery _) = ⊥

  module Run = Recovery.CheckedFor operation Success

  -- A lost reply after the publication cannot change either the token or time.
  committedReservationIsRecovered : ∀ key row before after reply →
    Observed.X.Completed (Observed.script key) (publish key row before) after reply →
    after ≡ publish key row before × reply ≡ reserved row
  committedReservationIsRecovered key row before after reply completion
    with Observed.completedObservation key (publish key row before) after reply completion
  ... | later , received , observed rewrite publishedReadable key row before =
    cong proj₁ observed , cong proj₂ observed

  reservationPreservesBusiness : ∀ key row before →
    Store.businessSnapshot (proj₁ (execute key row before)) ≡ Store.businessSnapshot before
  reservationPreservesBusiness key row before with inspect key before
  ... | vacant = refl
  ... | original saved = refl
  ... | broken token = refl

module Cancellation (postgres : PostgreSQL) where
  module C = Recovery.Cancellation

  execute : ℕ → ℤ → Store.World → Store.World × C.Result
  execute token timestamp = C.execute (C.input token timestamp)

  Received : ℕ → ℤ → Store.World → Set
  Received token timestamp before = ⊤

  available : ∀ token before → Σ ℤ (λ timestamp → Received token timestamp before)
  available token before = PostgreSQL.cancellationTimestamp postgres token before , tt

  -- The full intended state and the unchanged semantic reply are fixed by the
  -- existing cancellation contract. No caller supplies its expected answer.
  Goal : ℕ → Store.World → Store.World → C.Result → Set
  Goal token before after reply = Σ ℤ (λ timestamp →
    after ≡ C.intended (C.input token timestamp) before ×
    reply ≡ C.expectedReply (C.input token timestamp) before)

  meaning : ∀ token timestamp before → Received token timestamp before →
    Goal token before (proj₁ (execute token timestamp before)) (proj₂ (execute token timestamp before))
  meaning token timestamp before received = timestamp , cong proj₁ correct , cong proj₂ correct
    where correct = C.S.Statement.correct C.statement (C.input token timestamp) before

  module Observed = ReceiptStep ℕ ℤ C.Result execute Received available C.retryCannotChooseANewTime Goal meaning
  operation = Observed.operation
  module Run = Recovery.CheckedFor operation C.Success

  completedCancellationIsRecorded : ∀ token before after row →
    Observed.X.Completed (Observed.script token) before after (C.cancelled row) →
    Store.lookupCancellation after token ≡ just row
  completedCancellationIsRecorded token before after row completion
    with Observed.completedObservation token before after (C.cancelled row) completion
  ... | timestamp , received , observed =
    C.cancelledIsReadable (C.input token timestamp) before after row (sym observed)

  completedTargetIsPreserved = C.completedResultUnchanged
  committedPrefixIsPreserved = C.repliesUnchanged
  businessIsPreserved = C.everyReceiptPreservesBusiness

  -- The recorded control result supplies the guard required by every saved
  -- final business write. It cannot be replaced by a caller's cancellation flag.
  module FutureWrites (Input : Set) (token : Input → ℕ) (key : Input → Text)
    (resultKey : Text) (distinct : ∀ input → ¬ (key input ≡ resultKey))
    (apply : Input → Store.World → Store.World × Wire.Value)
    (keepsJournal : ∀ input before →
      Store.World.operations (proj₁ (apply input before)) ≡ Store.World.operations before) where
    module Saved = Recovery.StoreFinalStep Input token key resultKey distinct apply keepsJournal

    completedCancellationBlocksWrite : ∀ identity before after row →
      Observed.X.Completed (Observed.script identity) before after (C.cancelled row) →
      ∀ input → token input ≡ identity →
      Saved.execute input after ≡ (after , Saved.cancelled row)
    completedCancellationBlocksWrite identity before after row completion input same =
      Saved.cancellationBlocksEveryWrite input after row
        (trans (cong (Store.lookupCancellation after) same)
          (completedCancellationIsRecorded identity before after row completion))

  module FutureRegisteredWrites (Input Diagnostic : Set)
    (token : Input → ℕ) (key : Input → Text)
    (distinct : ∀ input → ¬ (key input ≡ StoreStep.resultKey))
    (decide : Input → Store.World → Diagnostic ⊎ (Store.World × Wire.Value))
    (keepsJournal : ∀ input before changed reply → decide input before ≡ inj₂ (changed , reply) →
      Store.World.operations changed ≡ Store.World.operations before)
    (admit : Input → StoreStep.Registration → Maybe Diagnostic) where
    module Saved = StoreStep.Admitted Input Diagnostic token key distinct decide keepsJournal admit

    -- Bad metadata can still ask for correction. Neither that branch nor an
    -- admitted cancelled step can publish another business change.
    completedCancellationBlocksPublication : ∀ identity before after row →
      Observed.X.Completed (Observed.script identity) before after (C.cancelled row) →
      ∀ input → token input ≡ identity → proj₁ (Saved.execute input after) ≡ after
    completedCancellationBlocksPublication identity before after row completion input same
      with admit input (StoreStep.registration after)
    ... | just diagnostic = refl
    ... | nothing rewrite trans (cong (Store.lookupCancellation after) same)
        (completedCancellationIsRecorded identity before after row completion) = refl

module Plan where
  record Boundary : Set where
    constructor boundary
    field site : Text; repeated : Bool

  record Step : Set where
    constructor step
    field site : Text; key : Maybe Text; id : Text

  record Saved : Set where
    constructor saved
    field operation : Text; shape : List Boundary; steps : List Step
          capture : Maybe Wire.Value -- missing differs from an explicitly present null

  record CapturedSource : Set where
    constructor capturedSource
    field id : Text; identity : ℕ; content : Text
          project : Maybe Text; alreadyEmbedded : Bool

  once repeated : String → Boundary
  once name = boundary (toList name) false
  repeated name = boundary (toList name) true

  entry : String → List Boundary → Text × List Boundary
  entry name boundaries = toList name , boundaries

  -- Mechanically checked against RegisteredOperation::named and its boundaries.
  -- REGISTERED-CONTROL-OPERATIONS
  registered : List (Text × List Boundary)
  registered =
    entry "insert_belief" (once "store.reserve_belief_preparation" ∷ once "store.publish_prepared_belief" ∷ []) ∷
    entry "delete_belief" (once "store.delete_belief" ∷ []) ∷
    entry "delete_project" (once "store.delete_project" ∷ []) ∷
    entry "delete_pattern" (once "store.delete_pattern" ∷ []) ∷
    entry "insert_pattern" (once "store.insert_pattern" ∷ []) ∷
    entry "record_support" (once "store.insert_edge" ∷ []) ∷
    entry "record_cause" (once "store.insert_edge" ∷ []) ∷
    entry "record_defeat" (once "store.insert_edge" ∷ once "store.propagate_locked" ∷ []) ∷
    entry "record_contradiction" (once "store.insert_contradicts" ∷ []) ∷
    entry "get_belief" [] ∷
    entry "list_beliefs" [] ∷
    entry "list_patterns" [] ∷
    entry "get_contradictions" [] ∷
    entry "decay_all" (once "store.decay_locked" ∷ []) ∷
    entry "sweep_expired_defeated" (repeated "store.delete_belief" ∷ []) ∷
    entry "query_relevant" [] ∷
    entry "add_evidence" (once "store.insert_evidence" ∷ []) ∷
    entry "get_evidence" [] ∷
    entry "propagate_from" (once "store.propagate_locked" ∷ []) ∷
    entry "query_intervention" [] ∷
    entry "load_document" (once "store.replace_document" ∷ repeated "store.insert_evidence" ∷ []) ∷
    entry "query_document" [] ∷
    entry "clear_document" (once "store.clear_document" ∷ []) ∷
    entry "learning_capabilities" [] ∷
    entry "get_lesson_assessment" [] ∷
    entry "lesson_assessment_history" [] ∷
    entry "explain_belief" [] ∷
    entry "get_learning_review" [] ∷
    entry "record_experience" (once "store.record_experience" ∷ []) ∷
    entry "pending_experiences" [] ∷
    entry "review_experience" (repeated "store.reserve_belief_preparation" ∷ once "store.review_experience_prepared" ∷ []) ∷
    entry "get_experience" [] ∷
    entry "experience_history" [] ∷
    entry "query_learning_context" [] ∷
    entry "delete_evidence" (once "store.delete_evidence" ∷ []) ∷
    entry "reembed" (repeated "store.insert_belief_embedding" ∷ []) ∷
    []

  lookup : Text → List (Text × List Boundary) → Maybe (List Boundary)
  lookup operation [] = nothing
  lookup operation ((name , boundaries) ∷ rest) with operation ≟Text name
  ... | yes _ = just boundaries
  ... | no _ = lookup operation rest

  -- Readback retains precisely these earlier committed-boundary layouts.
  -- They do not enter the current operation catalogue or authorize a new run.
  legacyRegistered : List (Text × List Boundary)
  legacyRegistered =
    entry "sweep_expired_defeated" (repeated "store.delete_belief" ∷ []) ∷
    entry "load_document" (once "store.replace_document" ∷ repeated "store.insert_evidence" ∷ []) ∷ []

  boolEqual : Bool → Bool → Bool
  boolEqual true true = true
  boolEqual false false = true
  boolEqual _ _ = false

  textEqual : Text → Text → Bool
  textEqual first second = does (first ≟Text second)

  maybeEqual : Maybe Text → Maybe Text → Bool
  maybeEqual nothing nothing = true
  maybeEqual (just first) (just second) = textEqual first second
  maybeEqual _ _ = false

  shapeEqual : List Boundary → List Boundary → Bool
  shapeEqual [] [] = true
  shapeEqual (first ∷ rest) (second ∷ tail) = textEqual (Boundary.site first) (Boundary.site second) ∧
    (boolEqual (Boundary.repeated first) (Boundary.repeated second) ∧ shapeEqual rest tail)
  shapeEqual _ _ = false

  stepsEqual : List Step → List Step → Bool
  stepsEqual [] [] = true
  stepsEqual (first ∷ rest) (second ∷ tail) = textEqual (Step.site first) (Step.site second) ∧
    (maybeEqual (Step.key first) (Step.key second) ∧
    (textEqual (Step.id first) (Step.id second) ∧ stepsEqual rest tail))
  stepsEqual _ _ = false

  readBoundary : Wire.Value → Validation.Fault ⊎ Boundary
  readBoundary = Decode.readRecord Objects.forbid Objects.rejectKnownRepeated
    (toList "site" ∷ toList "may_repeat" ∷ []) λ view →
    Decode._>>=_ (Wire.required (toList "site") Wire.asString view) λ site →
    Decode._>>=_ (Wire.required (toList "may_repeat") Wire.asBoolean view) λ repeat →
    inj₂ (boundary site repeat)

  readStep : Wire.Value → Validation.Fault ⊎ Step
  readStep = Decode.readRecord Objects.forbid Objects.rejectKnownRepeated
    (toList "site" ∷ toList "key" ∷ toList "id" ∷ []) λ view →
    Decode._>>=_ (Wire.required (toList "site") Wire.asString view) λ site →
    Decode._>>=_ (Wire.optional (toList "key") Wire.asString view) λ key →
    Decode._>>=_ (Wire.required (toList "id") Wire.asString view) λ id →
    inj₂ (step site key id)

  fieldNames : List Text
  fieldNames = toList "operation" ∷ toList "shape" ∷ toList "steps" ∷ toList "capture" ∷ []

  captureFieldNames : List Text
  captureFieldNames = toList "beliefs" ∷ []

  sourceFieldNames : List Text
  sourceFieldNames = toList "id" ∷ toList "content" ∷ toList "project" ∷ toList "already_embedded" ∷ []

  decode : Wire.Value → Validation.Fault ⊎ Saved
  decode = Decode.readRecord Objects.forbid Objects.rejectKnownRepeated
    fieldNames λ view →
    Decode._>>=_ (Wire.required (toList "operation") Wire.asString view) λ operation →
    Decode._>>=_ (Wire.required (toList "shape") (Decode.readArray readBoundary) view) λ shape →
    Decode._>>=_ (Wire.required (toList "steps") (Decode.readArray readStep) view) λ steps →
    inj₂ (saved operation shape steps (view (toList "capture")))

  readIdentity : Library.Contract → Wire.Value → Validation.Fault ⊎ (Text × ℕ)
  readIdentity library raw = Decode._>>=_ (Wire.asString raw) λ text → inspect text
    where
    inspect : Text → Validation.Fault ⊎ (Text × ℕ)
    inspect text with Library.Contract.parseUUID library text
    ... | nothing = inj₁ (Validation.fault [] Validation.malformedInput "The captured ID must be its original stored UUID.")
    ... | just id with textEqual text (Library.Contract.formatUUID library id)
    ... | false = inj₁ (Validation.fault [] Validation.malformedInput "The captured ID must use its original canonical stored spelling.")
    ... | true = inj₂ (text , PublicInput.uuidNumber id)

  readProject : Wire.Value → Validation.Fault ⊎ Maybe Text
  readProject Wire.null = inj₂ nothing
  readProject (Wire.string project) = inj₂ (just project)
  readProject _ = inj₁ (Validation.fault [] Validation.malformedInput "The captured project must be its original string or null.")

  readCapturedSource : Library.Contract → Wire.Value → Validation.Fault ⊎ CapturedSource
  readCapturedSource library = Decode.readRecord Objects.forbid Objects.rejectKnownRepeated sourceFieldNames λ view →
    Decode._>>=_ (Wire.required (toList "id") (readIdentity library) view) λ id →
    Decode._>>=_ (Wire.required (toList "content") Wire.asString view) λ content →
    Decode._>>=_ (Wire.required (toList "project") readProject view) λ project →
    Decode._>>=_ (Wire.required (toList "already_embedded") Wire.asBoolean view) λ embedded →
    inj₂ (capturedSource (proj₁ id) (proj₂ id) content project embedded)

  readCapture : Library.Contract → Wire.Value → Validation.Fault ⊎ List CapturedSource
  readCapture library = Decode.readRecord Objects.forbid Objects.rejectKnownRepeated captureFieldNames λ view →
    Wire.required (toList "beliefs") (Decode.readArray (readCapturedSource library)) view

  member : Text → List Text → Bool
  member key [] = false
  member key (first ∷ rest) = textEqual key first ∨ member key rest

  keys : Text → List Step → Maybe (List Text)
  keys site [] = just []
  keys site (item ∷ rest) with textEqual site (Step.site item)
  ... | false = keys site rest
  ... | true with Step.key item | keys site rest
  ... | nothing | _ = nothing
  ... | just key | nothing = nothing
  ... | just key | just later with textEqual (Text.trim key) key ∧
      (Text.nonblank key ∧ (does (Characters.noControls? key) ∧ not (member key later)))
  ... | false = nothing
  ... | true = just (key ∷ later)

  canonicalStep : Library.Contract → Text → Maybe Text → Step
  canonicalStep library site key = step site key
    (Library.Contract.lossyUTF8 library (Library.Contract.compactJSON library
      (Wire.array (Wire.string site ∷ encodedKey ∷ []))))
    where
    encodedKey = caseKey key
      where
      caseKey : Maybe Text → Wire.Value
      caseKey nothing = Wire.null
      caseKey (just text) = Wire.string text

  rebuild : Library.Contract → List Boundary → List Step → Maybe (List Step)
  rebuild library [] selected = just []
  rebuild library (item ∷ rest) selected with rebuild library rest selected
  ... | nothing = nothing
  ... | just tail with Boundary.repeated item
  ... | false = just (canonicalStep library (Boundary.site item) nothing ∷ tail)
  ... | true with keys (Boundary.site item) selected
  ... | nothing = nothing
  ... | just selectedKeys = just (map (λ key → canonicalStep library (Boundary.site item) (just key)) selectedKeys ++ tail)

  orderedAfter : ℕ → List CapturedSource → Bool
  orderedAfter previous [] = true
  orderedAfter previous (first ∷ rest) = does (previous <? CapturedSource.identity first) ∧
    orderedAfter (CapturedSource.identity first) rest

  captureOrdered : List CapturedSource → Bool
  captureOrdered [] = true
  captureOrdered (first ∷ rest) = orderedAfter (CapturedSource.identity first) rest

  pendingKeys : List CapturedSource → List Text
  pendingKeys [] = []
  pendingKeys (first ∷ rest) with CapturedSource.alreadyEmbedded first
  ... | true = pendingKeys rest
  ... | false = CapturedSource.id first ∷ pendingKeys rest

  pendingSteps : Library.Contract → List CapturedSource → List Step
  pendingSteps library rows = map
    (λ key → canonicalStep library (toList "store.insert_belief_embedding") (just key))
    (pendingKeys rows)

  captureMatches : Library.Contract → Saved → Bool
  captureMatches library plan with textEqual (Saved.operation plan) (toList "reembed")
  ... | false with Saved.capture plan
  ... | nothing = true
  ... | just _ = false
  captureMatches library plan | true with Saved.capture plan
  ... | nothing = false
  ... | just raw with readCapture library raw
  ... | inj₁ _ = false
  ... | inj₂ rows = captureOrdered rows ∧ stepsEqual (pendingSteps library rows) (Saved.steps plan)

  matchesBoundaries : Library.Contract → Saved → List Boundary → Bool
  matchesBoundaries library plan boundaries with shapeEqual boundaries (Saved.shape plan)
  ... | false = false
  ... | true with rebuild library boundaries (Saved.steps plan)
  ... | nothing = false
  ... | just expected = stepsEqual expected (Saved.steps plan)

  currentlyRegistered : Library.Contract → Saved → Bool
  currentlyRegistered library plan with lookup (Saved.operation plan) registered
  ... | nothing = false
  ... | just boundaries = matchesBoundaries library plan boundaries

  historicallyRegistered : Library.Contract → Saved → Bool
  historicallyRegistered library plan with lookup (Saved.operation plan) legacyRegistered
  ... | nothing = false
  ... | just boundaries = matchesBoundaries library plan boundaries

  structurallyValid : Library.Contract → Saved → Bool
  structurallyValid library plan = currentlyRegistered library plan ∨ historicallyRegistered library plan

  -- Past journals can be read without reinterpreting their steps as a new
  -- executable plan. Capture admission remains identical for both paths.
  valid : Library.Contract → Saved → Bool
  valid library plan = structurallyValid library plan ∧ captureMatches library plan

  executable : Library.Contract → Saved → Bool
  executable library plan = currentlyRegistered library plan ∧ captureMatches library plan

  obsoletePlanCannotResume : ∀ library plan → currentlyRegistered library plan ≡ false → executable library plan ≡ false
  obsoletePlanCannotResume library plan obsolete rewrite obsolete = refl

  currentPlanRemainsReadable : ∀ library plan → executable library plan ≡ true → valid library plan ≡ true
  currentPlanRemainsReadable library plan executablePlan with currentlyRegistered library plan | captureMatches library plan
  ... | false | _ with executablePlan
  ... | ()
  currentPlanRemainsReadable library plan executablePlan | true | false with executablePlan
  ... | ()
  currentPlanRemainsReadable library plan executablePlan | true | true = refl

  legacyPlanCompatibility : ∀ library plan →
    textEqual (Saved.operation plan) (toList "reembed") ≡ false → Saved.capture plan ≡ nothing →
    valid library plan ≡ structurallyValid library plan
  legacyPlanCompatibility library plan legacy absent rewrite legacy | absent
    with structurallyValid library plan
  ... | false = refl
  ... | true = refl

  legacyCaptureIsRejected : ∀ library plan raw →
    textEqual (Saved.operation plan) (toList "reembed") ≡ false → Saved.capture plan ≡ just raw →
    valid library plan ≡ false
  legacyCaptureIsRejected library plan raw legacy present rewrite legacy | present
    with structurallyValid library plan
  ... | false = refl
  ... | true = refl

  private
    andRight : ∀ first second → first ∧ second ≡ true → second ≡ true
    andRight false second ()
    andRight true second observed = observed

  -- A valid backfill plan selects exactly the original unembedded rows. This
  -- law is over every captured snapshot, not a chosen list or a work quota.
  validBackfillKeepsPendingSelection : ∀ library plan raw rows →
    textEqual (Saved.operation plan) (toList "reembed") ≡ true →
    Saved.capture plan ≡ just raw → readCapture library raw ≡ inj₂ rows →
    valid library plan ≡ true → stepsEqual (pendingSteps library rows) (Saved.steps plan) ≡ true
  validBackfillKeepsPendingSelection library plan raw rows isBackfill captured decoded accepted =
    selected acceptedCapture
    where
    acceptedCapture : captureMatches library plan ≡ true
    acceptedCapture = andRight (structurallyValid library plan) (captureMatches library plan) accepted
    selected : captureMatches library plan ≡ true → stepsEqual (pendingSteps library rows) (Saved.steps plan) ≡ true
    selected observed rewrite isBackfill | captured | decoded =
      andRight (captureOrdered rows) (stepsEqual (pendingSteps library rows) (Saved.steps plan)) observed

module Readback (library : Library.Contract) (postgres : PostgreSQL) where
  data Problem : Set where
    malformedPlan : Validation.Fault → Problem
    differentOperation invalidRegisteredPlan undeclaredOrNonprefixAnswers prematureCompletion : Problem

  data Result : Set where
    unknownToken reserved : Result
    awaitingPlan awaitingCompletion : Store.BindingRow → Result
    pending : Store.BindingRow → Plan.Step → List Store.SavedReplyRow → Result
    completed : Store.BindingRow → Wire.Value → Result
    needsRecovery : Store.BindingRow → Result
    inconsistent : Store.BindingRow → Problem → Result
    cancelled : Store.CancellationRow → Maybe Store.BindingRow → List Store.SavedReplyRow → Result

  savedRows : ℕ → Store.World → List Store.SavedReplyRow
  savedRows token before = filterᵇ (λ row → does (token ≟ Store.SavedReplyRow.token row))
    (Store.OperationTables.savedReplies (Store.World.operations before))

  insertOrdered : Store.SavedReplyRow → List Store.SavedReplyRow → List Store.SavedReplyRow
  insertOrdered row [] = row ∷ []
  insertOrdered row (first ∷ rest) with PostgreSQL.storedStepBefore postgres
    (Store.SavedReplyRow.step row) (Store.SavedReplyRow.step first)
  ... | true = row ∷ first ∷ rest
  ... | false = first ∷ insertOrdered row rest

  ordered : List Store.SavedReplyRow → List Store.SavedReplyRow
  ordered [] = []
  ordered (row ∷ rest) = insertOrdered row (ordered rest)

  find : Text → List Store.SavedReplyRow → Maybe Store.SavedReplyRow
  find key [] = nothing
  find key (row ∷ rest) with key ≟Text Store.SavedReplyRow.step row
  ... | yes _ = just row
  ... | no _ = find key rest

  prefix : List Plan.Step → List Store.SavedReplyRow → List Store.SavedReplyRow × List Plan.Step
  prefix [] rows = [] , []
  prefix steps@(first ∷ rest) rows with find (Plan.Step.id first) rows
  ... | nothing = [] , steps
  ... | just receipt with prefix rest rows
  ... | earlier , remaining = receipt ∷ earlier , remaining

  notFinal : Store.SavedReplyRow → Bool
  notFinal row = not (Plan.textEqual Recovery.Cancellation.resultKey (Store.SavedReplyRow.step row))

  afterPrefix : Store.BindingRow → Plan.Saved → List Store.SavedReplyRow →
    List Plan.Step → Maybe Store.SavedReplyRow → Result
  afterPrefix binding plan receipts remaining (just result) with remaining
  ... | [] = completed binding (Store.SavedReplyRow.reply result)
  ... | _ ∷ _ = inconsistent binding prematureCompletion
  afterPrefix binding plan receipts (next ∷ rest) nothing = pending binding next receipts
  afterPrefix binding plan receipts [] nothing with Plan.Saved.steps plan
  ... | [] = awaitingCompletion binding
  ... | _ ∷ _ = needsRecovery binding

  afterPlan : Store.BindingRow → Plan.Saved → List Store.SavedReplyRow → Result
  afterPlan binding plan rows with Plan.textEqual (Store.BindingRow.operation binding) (Plan.Saved.operation plan)
  ... | false = inconsistent binding differentOperation
  ... | true with Plan.valid library plan
  ... | false = inconsistent binding invalidRegisteredPlan
  ... | true with prefix (Plan.Saved.steps plan) rows
  ... | receipts , remaining with length (filterᵇ notFinal rows) ≟ length receipts
  ... | no _ = inconsistent binding undeclaredOrNonprefixAnswers
  ... | yes _ = afterPrefix binding plan receipts remaining (find Recovery.Cancellation.resultKey rows)

  differentOperationCannotComplete : ∀ binding plan rows →
    Plan.textEqual (Store.BindingRow.operation binding) (Plan.Saved.operation plan) ≡ false →
    afterPlan binding plan rows ≡ inconsistent binding differentOperation
  differentOperationCannotComplete binding plan rows mismatch rewrite mismatch = refl

  inspectBound : ℕ → Store.BindingRow → Store.World → Result
  inspectBound token binding before with Store.lookupCancellation before token
  ... | just receipt = cancelled receipt (just binding) (ordered (savedRows token before))
  ... | nothing with Project.Registered.plan token (Store.OperationTables.plans (Store.World.operations before))
  ... | nothing with savedRows token before
  ... | [] = awaitingPlan binding
  ... | _ ∷ _ = needsRecovery binding
  inspectBound token binding before | nothing | just raw with Plan.decode raw
  ... | inj₁ fault = inconsistent binding (malformedPlan fault)
  ... | inj₂ plan = afterPlan binding plan (savedRows token before)

  answer : ℕ → Store.World → Result
  answer token before with Project.Registered.binding token (Store.OperationTables.bindings (Store.World.operations before))
  ... | just binding = inspectBound token binding before
  ... | nothing with Store.lookupCancellation before token
  ... | just receipt = cancelled receipt nothing []
  ... | nothing with reservation token before
  ... | nothing = unknownToken
  ... | just row = reserved

  module Exact = Recovery.ReadOnly answer
  module Deterministic = Recovery.DeterministicContract Exact.operation
  operation = Deterministic.operationFor
  Goal = Deterministic.Goal

  -- A successful inspection retains the target's explicit pending/cancelled
  -- status. An inconsistent journal instead requires a repair decision.
  Success : Result → Set
  Success (inconsistent _ _) = ⊥
  Success (needsRecovery _) = ⊥
  Success _ = ⊤

  module Run = Recovery.CheckedFor operation Success
  everyInterruptedReadPreservesWorld = Exact.interruptedPreservesAllState
  completedRetryReturnsExactJournal = Exact.completedRetryPreservesStateAndAnswer

-- Internal request family: adding a control requires a concrete instance in
-- this total function. It does not advertise an MCP tool or accept raw scripts.
data Request : Set where reserve readOutcome cancel : Request

Input : Request → Set
Input reserve = RequestKey
Input readOutcome = ℕ
Input cancel = ℕ

module Controls (library : Library.Contract) (postgres : PostgreSQL) where
  module Reserve = Reservation postgres
  module Read = Readback library postgres
  module Cancel = Cancellation postgres

  Result : Request → Set
  Result reserve = Reserve.Result
  Result readOutcome = Read.Result
  Result cancel = Cancel.C.Result

  Goal : (request : Request) → Input request → Store.World → Store.World → Result request → Set
  Goal reserve = Reserve.Goal
  Goal readOutcome = Read.Goal
  Goal cancel = Cancel.Goal

  operation : (request : Request) → Recovery.RecoverableFor Store.World (Input request) (Result request) (Goal request)
  operation reserve = Reserve.operation
  operation readOutcome = Read.operation
  operation cancel = Cancel.operation

  Success : (request : Request) → Result request → Set
  Success reserve = Reserve.Success
  Success readOutcome = Read.Success
  Success cancel = Cancel.C.Success

  module Run (request : Request) = Recovery.CheckedFor (operation request) (Success request)
