{-# OPTIONS --safe #-}
-- Concrete operation controls. Request identities are admitted inputs;
-- PostgreSQL-generated metadata belongs to physical replies, never requests.
module Mimir.OperationControls where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_; _++_; map; filterᵇ; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_; all?)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_; _<?_; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String using (String; toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; sym; trans; subst)
open import Relation.Nullary using (Dec; ¬_; yes; no; does)
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
import Data.List.Relation.Unary.Any as Any
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
    entry "load_document" (once "store.prepare_document" ∷ once "store.replace_document" ∷ []) ∷
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

-- This is application-owned admission of the actual saved rows. Payload
-- decoding is supplied by the concrete handler; the shared raw readback uses
-- identity and therefore never interprets historical owner/result payloads.
alongObservation : ∀ {A B : Set} (original : A) (branch : (actual : A) → original ≡ actual → B)
  actual observed → branch original refl ≡ branch actual observed
alongObservation original branch .original refl = refl

differentSummands : ∀ {A B : Set} {first : A} {second : B} → inj₂ second ≡ inj₁ first → ⊥
differentSummands ()

journalMismatch : Validation.Fault
journalMismatch = Validation.fault (Validation.key "operation_token" ∷ []) Validation.wrongIdentity
  "The saved answers are not a complete prefix of the original operation plan. Read its original binding, plan and answers, then open the user dialog. Do not skip a step, invent a receipt or repeat completed work."

data Addressing : List Plan.Step → Set where
  empty : Addressing []
  more : ∀ {first rest} → All (λ later → Plan.Step.id first ≢ Plan.Step.id later) rest →
    Addressing rest → Addressing (first ∷ rest)

different? : ∀ first second → Dec (first ≢ second)
different? first second with first ≟Text second
... | yes same = no (λ different → different same)
... | no different = yes different

addressing? : (steps : List Plan.Step) → Dec (Addressing steps)
addressing? [] = yes empty
addressing? (first ∷ rest) with all? (λ later → different? (Plan.Step.id first) (Plan.Step.id later)) rest
... | no duplicate = no (λ { (more distinct _) → duplicate distinct })
... | yes distinct with addressing? rest
... | no duplicate = no (λ { (more _ addresses) → duplicate addresses })
... | yes addresses = yes (more distinct addresses)

module PrefixJournal (Payload : Set) (readPayload : Wire.Value → Validation.Fault ⊎ Payload) where
  publication : ℕ → Text → Payload → Wire.Value → Store.World → Store.World
  publication token key value raw before = Store.saveAnswer before token key raw

  publicationReadable : ∀ token key value raw before → Store.lookupSaved before token key ≡ nothing →
    Store.lookupSaved (publication token key value raw before) token key ≡ just raw
  publicationReadable token key value raw before absent rewrite absent = Store.headReplyReadable token key raw _

  publicationKeepsOldAnswer : ∀ token key value raw before queried address original →
    Store.lookupSaved before queried address ≡ just original →
    Store.lookupSaved (publication token key value raw before) queried address ≡ just original
  publicationKeepsOldAnswer token key value raw before queried address original known
    with Store.replyKey? queried address (Store.savedReplyRow token key raw)
  ... | no different = trans (Store.otherSavedAnswerPreserved before token key raw queried address different) known
  ... | yes (refl , refl) rewrite known = known

  missing? : ∀ token before declared → Dec (Store.lookupSaved before token (Plan.Step.id declared) ≡ nothing)
  missing? token before declared with Store.lookupSaved before token (Plan.Step.id declared)
  ... | nothing = yes refl
  ... | just _ = no (λ ())

  data Prefix (token : ℕ) (before : Store.World) : List Plan.Step → Set where
    waiting : ∀ {steps} → All (λ step → Store.lookupSaved before token (Plan.Step.id step) ≡ nothing) steps →
      Prefix token before steps
    saved : ∀ {first rest} → (raw : Wire.Value) (value : Payload) →
      Store.lookupSaved before token (Plan.Step.id first) ≡ just raw →
      readPayload raw ≡ inj₂ value → Prefix token before rest → Prefix token before (first ∷ rest)

  count : ∀ {token before steps} → Prefix token before steps → ℕ
  count (waiting _) = 0
  count (saved _ _ _ _ rest) = suc (count rest)

  allocations : ∀ {token before steps} → Prefix token before steps → List (Maybe Text × Payload)
  allocations (waiting _) = []
  allocations (saved {first} raw value known decoded rest) = (Plan.Step.key first , value) ∷ allocations rest

  read : ∀ token before steps → Validation.Fault ⊎ Prefix token before steps
  afterLookup : ∀ token before first rest observed → Store.lookupSaved before token (Plan.Step.id first) ≡ observed →
    Validation.Fault ⊎ Prefix token before (first ∷ rest)
  afterDecode : ∀ token before first rest raw → Store.lookupSaved before token (Plan.Step.id first) ≡ just raw →
    (observed : Validation.Fault ⊎ Payload) → readPayload raw ≡ observed → Validation.Fault ⊎ Prefix token before (first ∷ rest)
  afterMissing : ∀ token before steps → Dec (All (λ step → Store.lookupSaved before token (Plan.Step.id step) ≡ nothing) steps) →
    Validation.Fault ⊎ Prefix token before steps
  afterRest : ∀ token before first rest raw value → Store.lookupSaved before token (Plan.Step.id first) ≡ just raw →
    readPayload raw ≡ inj₂ value → Validation.Fault ⊎ Prefix token before rest → Validation.Fault ⊎ Prefix token before (first ∷ rest)
  read token before [] = inj₂ (waiting [])
  read token before (first ∷ rest) = afterLookup token before first rest (Store.lookupSaved before token (Plan.Step.id first)) refl
  afterLookup token before first rest nothing found = afterMissing token before (first ∷ rest) (all? (missing? token before) (first ∷ rest))
  afterLookup token before first rest (just raw) found = afterDecode token before first rest raw found (readPayload raw) refl
  afterMissing token before steps (no _) = inj₁ journalMismatch
  afterMissing token before steps (yes absent) = inj₂ (waiting absent)
  afterDecode token before first rest raw found (inj₁ fault) decoded = inj₁ fault
  afterDecode token before first rest raw found (inj₂ value) decoded = afterRest token before first rest raw value found decoded (read token before rest)
  afterRest token before first rest raw value found decoded (inj₁ fault) = inj₁ fault
  afterRest token before first rest raw value found decoded (inj₂ later) = inj₂ (saved raw value found decoded later)

  readAlong : ∀ token before first rest observed known → read token before (first ∷ rest) ≡ afterLookup token before first rest observed known
  readAlong token before first rest observed known = alongObservation _ (afterLookup token before first rest) observed known

  decodeAlong : ∀ token before first rest raw known observed decoded →
    afterLookup token before first rest (just raw) known ≡ afterDecode token before first rest raw known observed decoded
  decodeAlong token before first rest raw known observed decoded = alongObservation _ (afterDecode token before first rest raw known) observed decoded

  tokenRows : ℕ → Store.World → List Store.SavedReplyRow
  tokenRows token before = filterᵇ (λ row → does (token ≟ Store.SavedReplyRow.token row))
    (Store.OperationTables.savedReplies (Store.World.operations before))

  record Complete (token : ℕ) (before : Store.World) (steps : List Plan.Step) : Set where
    constructor complete
    field prefix : Prefix token before steps
          exactRows : length (tokenRows token before) ≡ count prefix
          declaredRows : All (λ row → Any.Any (λ declared → Store.SavedReplyRow.step row ≡ Plan.Step.id declared) steps) (tokenRows token before)

  declared? : ∀ steps row → Dec (Any.Any (λ declared → Store.SavedReplyRow.step row ≡ Plan.Step.id declared) steps)
  declared? steps row = Any.any? (λ declared → Store.SavedReplyRow.step row ≟Text Plan.Step.id declared) steps

  check : ∀ token before steps → Validation.Fault ⊎ Complete token before steps
  check token before steps with read token before steps
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ prefix with length (tokenRows token before) ≟ count prefix
  ... | no _ = inj₁ journalMismatch
  ... | yes exact with all? (declared? steps) (tokenRows token before)
  ... | no _ = inj₁ journalMismatch
  ... | yes known = inj₂ (complete prefix exact known)

  changedLookup : ∀ token declared value raw before queried → Plan.Step.id declared ≢ Plan.Step.id queried →
    Store.lookupSaved (publication token (Plan.Step.id declared) value raw before) token (Plan.Step.id queried) ≡
      Store.lookupSaved before token (Plan.Step.id queried)
  changedLookup token declared value raw before queried distinct =
    Store.otherSavedAnswerPreserved
      before
      token (Plan.Step.id declared) raw token (Plan.Step.id queried) (λ same → distinct (sym (proj₂ same)))

  missingSurvives : ∀ token declared value raw before rest →
    All (λ later → Plan.Step.id declared ≢ Plan.Step.id later) rest →
    All (λ later → Store.lookupSaved before token (Plan.Step.id later) ≡ nothing) rest →
    All (λ later → Store.lookupSaved (publication token (Plan.Step.id declared) value raw before)
      token (Plan.Step.id later) ≡ nothing) rest
  missingSurvives token declared value raw before [] [] [] = []
  missingSurvives token declared value raw before (later ∷ rest) (different ∷ distinct) (absent ∷ missing) =
    trans (changedLookup token declared value raw before later different) absent ∷
      missingSurvives token declared value raw before rest distinct missing

  -- Saving the next declared answer extends precisely the admitted prefix.
  extendWaiting : ∀ token before first rest value raw →
    Store.lookupSaved before token (Plan.Step.id first) ≡ nothing →
    readPayload raw ≡ inj₂ value →
    All (λ later → Plan.Step.id first ≢ Plan.Step.id later) rest →
    All (λ later → Store.lookupSaved before token (Plan.Step.id later) ≡ nothing) rest →
    Prefix token (publication token (Plan.Step.id first) value raw before) (first ∷ rest)
  extendWaiting token before first rest value raw absent decoded distinct missing = saved raw value
    (publicationReadable token (Plan.Step.id first) value raw before absent) decoded
    (waiting (missingSurvives token first value raw before rest distinct missing))

  next : ∀ {token before steps} → Prefix token before steps → Maybe Plan.Step
  next (waiting {[]} []) = nothing
  next (waiting {first ∷ rest} _) = just first
  next (saved _ _ _ _ rest) = next rest

  nextAbsent : ∀ {token before steps} (prefix : Prefix token before steps) first →
    next prefix ≡ just first → Store.lookupSaved before token (Plan.Step.id first) ≡ nothing
  nextAbsent (waiting {[]} []) first ()
  nextAbsent (waiting {first ∷ rest} (absent ∷ _)) .first refl = absent
  nextAbsent (saved _ _ _ _ rest) first selected = nextAbsent rest first selected

  nextProperty : ∀ {token before steps} (P : Plan.Step → Set) (prefix : Prefix token before steps) →
    All P steps → ∀ first → next prefix ≡ just first → P first
  nextProperty P (waiting {[]} []) [] first ()
  nextProperty P (waiting {first ∷ rest} _) (known ∷ _) .first refl = known
  nextProperty P (saved _ _ _ _ rest) (_ ∷ known) first selected = nextProperty P rest known first selected

  nextMember : ∀ {token before steps} (prefix : Prefix token before steps) first → next prefix ≡ just first →
    Any.Any (λ declared → Plan.Step.id first ≡ Plan.Step.id declared) steps
  nextMember (waiting {[]} []) first ()
  nextMember (waiting {first ∷ rest} _) .first refl = Any.here refl
  nextMember (saved _ _ _ _ rest) first selected = Any.there (nextMember rest first selected)

  sameNext : ∀ {token before steps} (first second : Prefix token before steps) → next first ≡ next second
  sameNext (waiting {[]} []) (waiting []) = refl
  sameNext (waiting {declared ∷ rest} _) (waiting _) = refl
  sameNext (waiting (absent ∷ _)) (saved _ _ known _ _) with trans (sym absent) known
  ... | ()
  sameNext (saved _ _ known _ _) (waiting (absent ∷ _)) with trans (sym absent) known
  ... | ()
  sameNext (saved _ _ _ _ earlier) (saved _ _ _ _ later) = sameNext earlier later

  sameCount : ∀ {token before steps} (first second : Prefix token before steps) → count first ≡ count second
  sameCount (waiting {[]} []) (waiting []) = refl
  sameCount (waiting {declared ∷ rest} _) (waiting _) = refl
  sameCount (waiting (absent ∷ _)) (saved _ _ known _ _) with trans (sym absent) known
  ... | ()
  sameCount (saved _ _ known _ _) (waiting (absent ∷ _)) with trans (sym absent) known
  ... | ()
  sameCount (saved _ _ _ _ earlier) (saved _ _ _ _ later) = cong suc (sameCount earlier later)

  readCannotFail : ∀ token before steps (prefix : Prefix token before steps) fault →
    read token before steps ≡ inj₁ fault → ⊥
  readCannotFail token before [] (waiting []) fault ()
  readCannotFail token before (first ∷ rest) (waiting missing@(absent ∷ _)) fault failed
    with all? (missing? token before) (first ∷ rest) in inspected
  ... | no gap = gap missing
  ... | yes returned = differentSummands (trans (sym (trans
    (readAlong token before first rest nothing absent)
    (cong (afterMissing token before (first ∷ rest)) inspected))) failed)
  readCannotFail token before (first ∷ rest) (saved raw value known decoded later) fault failed
    with read token before rest in observed
  ... | inj₁ diagnosticFault = readCannotFail token before rest later diagnosticFault observed
  ... | inj₂ _ = differentSummands (trans
    (sym (trans (readAlong token before first rest (just raw) known)
      (trans (decodeAlong token before first rest raw known (inj₂ value) decoded)
        (cong (afterRest token before first rest raw value known decoded) observed)))) failed)

  checkCannotFail : ∀ token before steps (journal : Complete token before steps) fault →
    check token before steps ≡ inj₁ fault → ⊥
  checkCannotFail token before steps (complete prefix exact declaredRows) fault failed
    with read token before steps in observed
  ... | inj₁ diagnosticFault = readCannotFail token before steps prefix diagnosticFault observed
  ... | inj₂ actual with length (tokenRows token before) ≟ count actual
  ... | no incorrect = incorrect (trans exact (sameCount prefix actual))
  ... | yes _ with all? (declared? steps) (tokenRows token before)
  ... | no unknown = unknown declaredRows
  ... | yes _ with failed
  ... | ()

  -- A loop cursor records that every preceding declaration already has its
  -- saved answer. It never authorizes jumping over an absent predecessor.
  data Cursor (token : ℕ) (before : Store.World) : List Plan.Step → List Plan.Step → Set where
    here : ∀ remaining → Cursor token before remaining remaining
    passed : ∀ first rest remaining raw → Store.lookupSaved before token (Plan.Step.id first) ≡ just raw →
      Cursor token before rest remaining → Cursor token before (first ∷ rest) remaining

  cursorNext : ∀ token before full first rest → (prefix : Prefix token before full) →
    Cursor token before full (first ∷ rest) → Store.lookupSaved before token (Plan.Step.id first) ≡ nothing →
    next prefix ≡ just first
  cursorNext token before .(first ∷ rest) first rest (waiting (_ ∷ _)) (here _) absent = refl
  cursorNext token before .(first ∷ rest) first rest (saved _ _ known _ _) (here _) absent
    with trans (sym absent) known
  ... | ()
  cursorNext token before .(previous ∷ prior) first rest (waiting (missing ∷ _))
    (passed previous prior .(first ∷ rest) raw known cursor) absent with trans (sym missing) known
  ... | ()
  cursorNext token before .(previous ∷ prior) first rest (saved _ _ _ _ prefix)
    (passed previous prior .(first ∷ rest) raw known cursor) absent = cursorNext token before prior first rest prefix cursor absent

  cursorDecoded : ∀ token before full first rest raw → Prefix token before full →
    Cursor token before full (first ∷ rest) → Store.lookupSaved before token (Plan.Step.id first) ≡ just raw →
    Σ Payload (λ value → readPayload raw ≡ inj₂ value)
  cursorDecoded token before .(first ∷ rest) first rest raw (waiting (missing ∷ _)) (here _) known
    with trans (sym missing) known
  ... | ()
  cursorDecoded token before .(first ∷ rest) first rest raw (saved savedRaw value savedKnown decoded _) (here _) known
    with trans (sym savedKnown) known
  ... | refl = value , decoded
  cursorDecoded token before .(previous ∷ prior) first rest raw (waiting (missing ∷ _))
    (passed previous prior .(first ∷ rest) old original cursor) known with trans (sym missing) original
  ... | ()
  cursorDecoded token before .(previous ∷ prior) first rest raw (saved _ _ _ _ prefix)
    (passed previous prior .(first ∷ rest) old original cursor) known = cursorDecoded token before prior first rest raw prefix cursor known

  cursorFinished : ∀ token before full → (prefix : Prefix token before full) → Cursor token before full [] → next prefix ≡ nothing
  cursorFinished token before [] (waiting []) (here []) = refl
  cursorFinished token before .(previous ∷ prior) (waiting (missing ∷ _))
    (passed previous prior [] raw known cursor) with trans (sym missing) known
  ... | ()
  cursorFinished token before .(previous ∷ prior) (saved _ _ _ _ prefix)
    (passed previous prior [] raw known cursor) = cursorFinished token before prior prefix cursor

  cursorAddresses : ∀ {token before full remaining} → Addressing full → Cursor token before full remaining → Addressing remaining
  cursorAddresses addresses (here _) = addresses
  cursorAddresses (more _ addresses) (passed _ _ _ _ _ cursor) = cursorAddresses addresses cursor

  futureMissing : ∀ token before full first rest → (prefix : Prefix token before full) →
    Cursor token before full (first ∷ rest) → next prefix ≡ just first →
    All (λ declared → Store.lookupSaved before token (Plan.Step.id declared) ≡ nothing) rest
  futureMissing token before .(first ∷ rest) first rest (waiting (_ ∷ missing)) (here _) selected = missing
  futureMissing token before .(first ∷ rest) first rest prefix@(saved _ _ known _ _) (here _) selected
    with trans (sym (nextAbsent prefix first selected)) known
  ... | ()
  futureMissing token before .(previous ∷ prior) first rest (waiting (missing ∷ _))
    (passed previous prior .(first ∷ rest) raw known cursor) selected with trans (sym missing) known
  ... | ()
  futureMissing token before .(previous ∷ prior) first rest (saved _ _ _ _ prefix)
    (passed previous prior .(first ∷ rest) raw known cursor) selected = futureMissing token before prior first rest prefix cursor selected

  transportCursor : ∀ token before after full remaining →
    (∀ key raw → Store.lookupSaved before token key ≡ just raw → Store.lookupSaved after token key ≡ just raw) →
    Cursor token before full remaining → Cursor token after full remaining
  transportCursor token before after full .full kept (here .full) = here full
  transportCursor token before after .(first ∷ rest) remaining kept (passed first rest .remaining raw known cursor) =
    passed first rest remaining raw (kept (Plan.Step.id first) raw known)
      (transportCursor token before after rest remaining kept cursor)

  advanceCursor : ∀ token before full first rest raw →
    Cursor token before full (first ∷ rest) → Store.lookupSaved before token (Plan.Step.id first) ≡ just raw →
    Cursor token before full rest
  advanceCursor token before .(first ∷ rest) first rest raw (here _) known = passed first rest rest raw known (here rest)
  advanceCursor token before .(previous ∷ prior) first rest raw
    (passed previous prior .(first ∷ rest) originalValue original cursor) known =
    passed previous prior rest originalValue original (advanceCursor token before prior first rest raw cursor known)

  extend : ∀ token before steps (prefix : Prefix token before steps) first value raw →
    Addressing steps → next prefix ≡ just first → readPayload raw ≡ inj₂ value →
    Σ (Prefix token (publication token (Plan.Step.id first) value raw before) steps)
      (λ advanced → count advanced ≡ suc (count prefix))
  extend token before [] (waiting []) first value raw empty () decoded
  extend token before (first ∷ rest) (waiting (absent ∷ missing)) .first value raw
    (more distinct addresses) refl decoded =
      extendWaiting token before first rest value raw absent decoded distinct missing , refl
  extend token before (previous ∷ rest) (saved original earlier known represented prefix) first value raw
    (more distinct addresses) selected decoded
    with extend token before rest prefix first value raw addresses selected decoded
  ... | advanced , grew = saved original earlier
      (publicationKeepsOldAnswer token (Plan.Step.id first) value raw before token (Plan.Step.id previous) original known)
      represented advanced , cong suc grew

  sameToken : ∀ queried → does (queried ≟ queried) ≡ true
  sameToken zero = refl
  sameToken (suc queried) = sameToken queried

  publicationCount : ∀ token before first value raw →
    Store.lookupSaved before token (Plan.Step.id first) ≡ nothing →
    length (tokenRows token (publication token (Plan.Step.id first) value raw before)) ≡
      suc (length (tokenRows token before))
  publicationCount token before first value raw absent rewrite absent | sameToken token = refl

  publicationRows : ∀ token before first value raw → Store.lookupSaved before token (Plan.Step.id first) ≡ nothing →
    tokenRows token (publication token (Plan.Step.id first) value raw before) ≡ Store.savedReplyRow token (Plan.Step.id first) raw ∷ tokenRows token before
  publicationRows token before first value raw absent rewrite absent | sameToken token = refl

  extendComplete : ∀ token before steps (journal : Complete token before steps) first value raw →
    Addressing steps → next (Complete.prefix journal) ≡ just first → readPayload raw ≡ inj₂ value →
    Complete token (publication token (Plan.Step.id first) value raw before) steps
  extendComplete token before steps (complete prefix exact declaredRows) first value raw addresses selected decoded
    with extend token before steps prefix first value raw addresses selected decoded
  ... | advanced , grew = complete advanced (trans
    (publicationCount token before first value raw (nextAbsent prefix first selected))
    (trans (cong suc exact) (sym grew)))
    (subst (All (λ row → Any.Any (λ declared → Store.SavedReplyRow.step row ≡ Plan.Step.id declared) steps))
      (sym (publicationRows token before first value raw (nextAbsent prefix first selected)))
      (nextMember prefix first selected ∷ declaredRows))

  moveMissing : ∀ token before after steps →
    (∀ key → Store.lookupSaved after token key ≡ Store.lookupSaved before token key) →
    All (λ declared → Store.lookupSaved before token (Plan.Step.id declared) ≡ nothing) steps →
    All (λ declared → Store.lookupSaved after token (Plan.Step.id declared) ≡ nothing) steps
  moveMissing token before after [] same [] = []
  moveMissing token before after (first ∷ rest) same (known ∷ missing) =
    trans (same (Plan.Step.id first)) known ∷ moveMissing token before after rest same missing

  relocatePrefix : ∀ token before after steps →
    (∀ key → Store.lookupSaved after token key ≡ Store.lookupSaved before token key) →
    (original : Prefix token before steps) → Σ (Prefix token after steps)
      (λ moved → count moved ≡ count original × next moved ≡ next original)
  relocatePrefix token before after [] same (waiting []) = waiting [] , refl , refl
  relocatePrefix token before after (first ∷ rest) same (waiting missing) =
    waiting (moveMissing token before after (first ∷ rest) same missing) , refl , refl
  relocatePrefix token before after (first ∷ rest) same (saved raw value known decoded prefix)
    with relocatePrefix token before after rest same prefix
  ... | moved , sameCount , sameNext = saved raw value (trans (same (Plan.Step.id first)) known) decoded moved , cong suc sameCount , sameNext

  relocateComplete : ∀ token before after steps → Store.World.operations after ≡ Store.World.operations before →
    (journal : Complete token before steps) → Σ (Complete token after steps)
      (λ moved → next (Complete.prefix moved) ≡ next (Complete.prefix journal))
  relocateComplete token before after steps same (complete prefix exact declaredRows)
    with relocatePrefix token before after steps
      (λ key → cong (λ tables → Store.lookupReply token key (Store.OperationTables.savedReplies tables)) same) prefix
  ... | moved , sameCount , sameNext = complete moved
    (trans (cong (λ tables → length (filterᵇ (λ row → does (token ≟ Store.SavedReplyRow.token row))
      (Store.OperationTables.savedReplies tables))) same) (trans exact (sym sameCount)))
    (subst (All (λ row → Any.Any (λ declared → Store.SavedReplyRow.step row ≡ Plan.Step.id declared) steps))
      (sym (cong (λ tables → filterᵇ (λ row → does (token ≟ Store.SavedReplyRow.token row)) (Store.OperationTables.savedReplies tables)) same)) declaredRows) , sameNext

  retainCompletedPrefix : ∀ token before steps (prefix : Prefix token before steps) key raw →
    next prefix ≡ nothing → All (λ declared → Plan.Step.id declared ≢ key) steps →
    Σ (Prefix token (Store.saveAnswer before token key raw) steps)
      (λ moved → next moved ≡ nothing × count moved ≡ count prefix)
  retainCompletedPrefix token before [] (waiting []) key raw finished [] = waiting [] , refl , refl
  retainCompletedPrefix token before (first ∷ rest) (waiting _) key raw () different
  retainCompletedPrefix token before (first ∷ rest) (saved original value known decoded prefix) key raw finished (different ∷ distinct)
    with retainCompletedPrefix token before rest prefix key raw finished distinct
  ... | moved , finishedMoved , sameCount = saved original value
    (trans (Store.otherSavedAnswerPreserved before token key raw token (Plan.Step.id first)
      (λ same → different (proj₂ same))) known) decoded moved , finishedMoved , cong suc sameCount

module OpaqueJournal = PrefixJournal Wire.Value inj₂

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

  replyValue : Maybe Store.SavedReplyRow → Maybe Wire.Value
  replyValue nothing = nothing
  replyValue (just row) = just (Store.SavedReplyRow.reply row)

  doesTrue : ∀ {P : Set} (decision : Dec P) → P → does decision ≡ true
  doesTrue (yes _) known = refl
  doesTrue (no impossible) known = ⊥-elim (impossible known)

  doesFalse : ∀ {P : Set} (decision : Dec P) → ¬ P → does decision ≡ false
  doesFalse (yes impossible) absent = ⊥-elim (absent impossible)
  doesFalse (no _) absent = refl

  -- The displayed ordered prefix and the transaction's saved-answer lookup
  -- read the same actual token/key rows. Payloads remain completely opaque.
  findReply : ∀ token key rows → replyValue
    (find key (filterᵇ (λ row → does (token ≟ Store.SavedReplyRow.token row)) rows)) ≡ Store.lookupReply token key rows
  findReply token key [] = refl
  findReply token key (row ∷ rest) with token ≟ Store.SavedReplyRow.token row
  ... | no different rewrite doesFalse (token ≟ Store.SavedReplyRow.token row) different = findReply token key rest
  ... | yes same with key ≟Text Store.SavedReplyRow.step row in keySeen
  ... | no different rewrite doesTrue (token ≟ Store.SavedReplyRow.token row) same | keySeen = findReply token key rest
  ... | yes _ rewrite doesTrue (token ≟ Store.SavedReplyRow.token row) same | keySeen = refl

  declaredDifferent : ∀ key steps row → All (λ declared → Plan.Step.id declared ≢ key) steps →
    Any.Any (λ declared → Store.SavedReplyRow.step row ≡ Plan.Step.id declared) steps → Store.SavedReplyRow.step row ≢ key
  declaredDifferent key (first ∷ rest) row (different ∷ _) (Any.here same) equal = different (trans (sym same) equal)
  declaredDifferent key (first ∷ rest) row (_ ∷ distinct) (Any.there later) = declaredDifferent key rest row distinct later

  differentRows : ∀ key steps rows → All (λ declared → Plan.Step.id declared ≢ key) steps →
    All (λ row → Any.Any (λ declared → Store.SavedReplyRow.step row ≡ Plan.Step.id declared) steps) rows →
    All (λ row → Store.SavedReplyRow.step row ≢ key) rows
  differentRows key steps [] distinct [] = []
  differentRows key steps (row ∷ rows) distinct (declared ∷ known) =
    declaredDifferent key steps row distinct declared ∷ differentRows key steps rows distinct known

  findMissing : ∀ key rows → All (λ row → Store.SavedReplyRow.step row ≢ key) rows → find key rows ≡ nothing
  findMissing key [] [] = refl
  findMissing key (row ∷ rows) (different ∷ distinct) with key ≟Text Store.SavedReplyRow.step row
  ... | yes same = ⊥-elim (different (sym same))
  ... | no _ = findMissing key rows distinct

  findAbsentSaved : ∀ token before key → Store.lookupSaved before token key ≡ nothing → find key (savedRows token before) ≡ nothing
  findAbsentSaved token before key absent with find key (savedRows token before) in observed
  ... | nothing = refl
  ... | just row with trans (sym (cong replyValue observed))
    (trans (findReply token key (Store.OperationTables.savedReplies (Store.World.operations before))) absent)
  ... | ()

  undeclaredAbsent : ∀ token before steps (journal : OpaqueJournal.Complete token before steps) key →
    All (λ declared → Plan.Step.id declared ≢ key) steps → Store.lookupSaved before token key ≡ nothing
  undeclaredAbsent token before steps journal key distinct = trans
    (sym (findReply token key (Store.OperationTables.savedReplies (Store.World.operations before))))
    (cong replyValue (findMissing key (savedRows token before)
      (differentRows key steps (savedRows token before) distinct (OpaqueJournal.Complete.declaredRows journal))))

  withoutAbsentKey : ∀ token key rows → Store.lookupReply token key rows ≡ nothing →
    filterᵇ (λ row → not (Plan.textEqual key (Store.SavedReplyRow.step row)))
      (filterᵇ (λ row → does (token ≟ Store.SavedReplyRow.token row)) rows) ≡
    filterᵇ (λ row → does (token ≟ Store.SavedReplyRow.token row)) rows
  withoutAbsentKey token key [] absent = refl
  withoutAbsentKey token key (row ∷ rest) absent with token ≟ Store.SavedReplyRow.token row
  ... | no different rewrite doesFalse (token ≟ Store.SavedReplyRow.token row) different = withoutAbsentKey token key rest absent
  ... | yes same with key ≟Text Store.SavedReplyRow.step row in keySeen
  ... | yes sameKey rewrite doesTrue (token ≟ Store.SavedReplyRow.token row) same | keySeen with absent
  ... | ()
  withoutAbsentKey token key (row ∷ rest) absent | yes same | no different
    rewrite doesTrue (token ≟ Store.SavedReplyRow.token row) same |
      doesFalse (key ≟Text Store.SavedReplyRow.step row) different =
    cong (row ∷_) (withoutAbsentKey token key rest absent)

  savedRowsAfterInsert : ∀ token before key raw → Store.lookupSaved before token key ≡ nothing →
    savedRows token (Store.saveAnswer before token key raw) ≡ Store.savedReplyRow token key raw ∷ savedRows token before
  savedRowsAfterInsert token before key raw absent rewrite absent | OpaqueJournal.sameToken token = refl

  findInsertedResult : ∀ token before raw → Store.lookupSaved before token StoreStep.resultKey ≡ nothing →
    find StoreStep.resultKey (savedRows token (Store.saveAnswer before token StoreStep.resultKey raw)) ≡ just (Store.savedReplyRow token StoreStep.resultKey raw)
  findInsertedResult token before raw absent rewrite savedRowsAfterInsert token before StoreStep.resultKey raw absent
    with StoreStep.resultKey ≟Text StoreStep.resultKey
  ... | yes _ = refl
  ... | no impossible = ⊥-elim (impossible refl)

  prefix : List Plan.Step → List Store.SavedReplyRow → List Store.SavedReplyRow × List Plan.Step
  prefix [] rows = [] , []
  prefix steps@(first ∷ rest) rows with find (Plan.Step.id first) rows
  ... | nothing = [] , steps
  ... | just receipt with prefix rest rows
  ... | earlier , remaining = receipt ∷ earlier , remaining

  prefixComplete : ∀ token before steps (journal : OpaqueJournal.Prefix token before steps) →
    OpaqueJournal.next journal ≡ nothing →
    Σ (List Store.SavedReplyRow) (λ receipts →
      prefix steps (savedRows token before) ≡ (receipts , []) × length receipts ≡ OpaqueJournal.count journal)
  prefixComplete token before [] (OpaqueJournal.waiting []) finished = [] , refl , refl
  prefixComplete token before (first ∷ rest) (OpaqueJournal.waiting _) ()
  prefixComplete token before (first ∷ rest) (OpaqueJournal.saved raw value known decoded later) finished
    with find (Plan.Step.id first) (savedRows token before) in found
  ... | nothing with trans (sym (cong replyValue found)) (trans (findReply token (Plan.Step.id first)
      (Store.OperationTables.savedReplies (Store.World.operations before))) known)
  ... | ()
  prefixComplete token before (first ∷ rest) (OpaqueJournal.saved raw value known decoded later) finished | just row
    with prefixComplete token before rest later finished
  ... | receipts , complete , sameCount rewrite complete = (row ∷ receipts) , refl , cong suc sameCount

  remainingHead : List Plan.Step → Maybe Plan.Step
  remainingHead [] = nothing
  remainingHead (first ∷ _) = just first

  prefixObservation : ∀ token before steps (journal : OpaqueJournal.Prefix token before steps) →
    Σ (List Store.SavedReplyRow) (λ receipts → Σ (List Plan.Step) (λ remaining →
      prefix steps (savedRows token before) ≡ (receipts , remaining) ×
      length receipts ≡ OpaqueJournal.count journal × OpaqueJournal.next journal ≡ remainingHead remaining))
  prefixObservation token before [] (OpaqueJournal.waiting []) = [] , [] , refl , refl , refl
  prefixObservation token before (first ∷ rest) (OpaqueJournal.waiting (absent ∷ later))
    with find (Plan.Step.id first) (savedRows token before) in found
  ... | nothing = [] , (first ∷ rest) , refl , refl , refl
  ... | just row with trans (sym (cong replyValue found))
    (trans (findReply token (Plan.Step.id first) (Store.OperationTables.savedReplies (Store.World.operations before))) absent)
  ... | ()
  prefixObservation token before (first ∷ rest) (OpaqueJournal.saved raw value known decoded later)
    with find (Plan.Step.id first) (savedRows token before) in found
  ... | nothing with trans (sym (cong replyValue found))
    (trans (findReply token (Plan.Step.id first) (Store.OperationTables.savedReplies (Store.World.operations before))) known)
  ... | ()
  prefixObservation token before (first ∷ rest) (OpaqueJournal.saved raw value known decoded later) | just row
    with prefixObservation token before rest later
  ... | receipts , remaining , observed , sameCount , sameNext rewrite observed =
    (row ∷ receipts) , remaining , refl , cong suc sameCount , sameNext

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

  afterPlanCompletes : ∀ binding plan rows receipts result →
    Plan.textEqual (Store.BindingRow.operation binding) (Plan.Saved.operation plan) ≡ true →
    Plan.valid library plan ≡ true → prefix (Plan.Saved.steps plan) rows ≡ (receipts , []) →
    length (filterᵇ notFinal rows) ≡ length receipts → find StoreStep.resultKey rows ≡ just result →
    afterPlan binding plan rows ≡ completed binding (Store.SavedReplyRow.reply result)
  afterPlanCompletes binding plan rows receipts result sameOperation validPlan full exact resultSaved
    rewrite sameOperation | validPlan | full with length (filterᵇ notFinal rows) ≟ length receipts
  ... | no different = ⊥-elim (different exact)
  ... | yes _ rewrite resultSaved = refl

  afterPlanPending : ∀ binding plan rows receipts next rest →
    Plan.textEqual (Store.BindingRow.operation binding) (Plan.Saved.operation plan) ≡ true →
    Plan.valid library plan ≡ true → prefix (Plan.Saved.steps plan) rows ≡ (receipts , next ∷ rest) →
    length (filterᵇ notFinal rows) ≡ length receipts → find StoreStep.resultKey rows ≡ nothing →
    afterPlan binding plan rows ≡ pending binding next receipts
  afterPlanPending binding plan rows receipts next rest sameOperation validPlan prefixKnown exact resultAbsent
    rewrite sameOperation | validPlan | prefixKnown with length (filterᵇ notFinal rows) ≟ length receipts
  ... | no different = ⊥-elim (different exact)
  ... | yes _ rewrite resultAbsent = refl

  pendingAfterPrefix : ∀ token before binding plan next →
    (journal : OpaqueJournal.Complete token before (Plan.Saved.steps plan)) →
    OpaqueJournal.next (OpaqueJournal.Complete.prefix journal) ≡ just next →
    Store.lookupSaved before token StoreStep.resultKey ≡ nothing →
    Plan.textEqual (Store.BindingRow.operation binding) (Plan.Saved.operation plan) ≡ true → Plan.valid library plan ≡ true →
    Σ (List Store.SavedReplyRow) (λ receipts → afterPlan binding plan (savedRows token before) ≡ pending binding next receipts)
  pendingAfterPrefix token before binding plan next journal selected absent sameOperation validPlan
    with prefixObservation token before (Plan.Saved.steps plan) (OpaqueJournal.Complete.prefix journal)
  ... | receipts , [] , known , sameCount , sameNext with trans (sym selected) sameNext
  ... | ()
  pendingAfterPrefix token before binding plan next journal selected absent sameOperation validPlan
    | receipts , (first ∷ rest) , known , sameCount , sameNext with trans (sym selected) sameNext
  ... | refl = receipts , afterPlanPending binding plan _ receipts next rest sameOperation validPlan known
    (trans (cong length (withoutAbsentKey token StoreStep.resultKey
      (Store.OperationTables.savedReplies (Store.World.operations before)) absent))
      (trans (OpaqueJournal.Complete.exactRows journal) (sym sameCount)))
    (findAbsentSaved token before StoreStep.resultKey absent)

  nonfinalCountAfterResult : ∀ token before value → Store.lookupSaved before token StoreStep.resultKey ≡ nothing →
    length (filterᵇ notFinal (savedRows token (Store.saveAnswer before token StoreStep.resultKey value))) ≡ length (savedRows token before)
  nonfinalCountAfterResult token before value absent
    rewrite savedRowsAfterInsert token before StoreStep.resultKey value absent |
      doesTrue (StoreStep.resultKey ≟Text StoreStep.resultKey) refl |
      withoutAbsentKey token StoreStep.resultKey (Store.OperationTables.savedReplies (Store.World.operations before)) absent = refl

  completedAfterResult : ∀ token before binding plan value →
    (journal : OpaqueJournal.Complete token before (Plan.Saved.steps plan)) → OpaqueJournal.next (OpaqueJournal.Complete.prefix journal) ≡ nothing →
    All (λ declared → Plan.Step.id declared ≢ StoreStep.resultKey) (Plan.Saved.steps plan) →
    Store.lookupSaved before token StoreStep.resultKey ≡ nothing →
    Plan.textEqual (Store.BindingRow.operation binding) (Plan.Saved.operation plan) ≡ true → Plan.valid library plan ≡ true →
    afterPlan binding plan (savedRows token (Store.saveAnswer before token StoreStep.resultKey value)) ≡ completed binding value
  completedAfterResult token before binding plan value journal finished distinct absent sameOperation validPlan
    with OpaqueJournal.retainCompletedPrefix token before (Plan.Saved.steps plan) (OpaqueJournal.Complete.prefix journal)
      StoreStep.resultKey value finished distinct
  ... | moved , complete , sameCount with prefixComplete token (Store.saveAnswer before token StoreStep.resultKey value) (Plan.Saved.steps plan) moved complete
  ... | receipts , full , exact = afterPlanCompletes binding plan _ receipts (Store.savedReplyRow token StoreStep.resultKey value)
    sameOperation validPlan full
    (trans (nonfinalCountAfterResult token before value absent)
      (trans (OpaqueJournal.Complete.exactRows journal) (trans (sym sameCount) (sym exact))))
    (findInsertedResult token before value absent)

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

  -- This execution context is built from actual rows. It is never an input
  -- supplied by an agent or a handler claiming that an arbitrary plan is safe.
  record ExecutionContext (operation : Text) (token : ℕ) (before : Store.World) : Set where
    constructor executionContext
    field
      reservationRow : Store.ReservationRow
      originalReservation : reservation token before ≡ just reservationRow
      bindingRow : Store.BindingRow
      originalBinding : Project.Registered.binding token
        (Store.OperationTables.bindings (Store.World.operations before)) ≡ just bindingRow
      requestedOperation : Plan.textEqual (Store.BindingRow.operation bindingRow) operation ≡ true
      rawPlan : Wire.Value
      originalPlan : Project.Registered.plan token
        (Store.OperationTables.plans (Store.World.operations before)) ≡ just rawPlan
      plan : Plan.Saved
      decoded : Plan.decode rawPlan ≡ inj₂ plan
      matchingOperation : Plan.textEqual (Store.BindingRow.operation bindingRow) (Plan.Saved.operation plan) ≡ true
      executable : Plan.executable library plan ≡ true
      addresses : Addressing (Plan.Saved.steps plan)
      separateResult : All (λ declared → Plan.Step.id declared ≢ StoreStep.resultKey) (Plan.Saved.steps plan)
      journal : OpaqueJournal.Complete token before (Plan.Saved.steps plan)

  data ExecutionAdmission (operation : Text) (token : ℕ) (before : Store.World) : Set where
    returned : Result → ExecutionAdmission operation token before
    admitted : ExecutionContext operation token before → ExecutionAdmission operation token before

  sameJust : ∀ {A : Set} {first second : A} → just first ≡ just second → first ≡ second
  sameJust refl = refl

  sameRight : ∀ {A B : Set} {first second : B} → inj₂ {A = A} first ≡ inj₂ second → first ≡ second
  sameRight refl = refl

  noJust : ∀ {A : Set} {value : A} → nothing ≡ just value → ⊥
  noJust ()

  falseTrue : false ≡ true → ⊥
  falseTrue ()

  knownRaw : ∀ operation token before (context : ExecutionContext operation token before) raw →
    Project.Registered.plan token (Store.OperationTables.plans (Store.World.operations before)) ≡ just raw →
    ExecutionContext.rawPlan context ≡ raw
  knownRaw operation token before context raw observed = sameJust (trans (sym (ExecutionContext.originalPlan context)) observed)

  knownPlan : ∀ operation token before (context : ExecutionContext operation token before) raw plan →
    Project.Registered.plan token (Store.OperationTables.plans (Store.World.operations before)) ≡ just raw →
    Plan.decode raw ≡ inj₂ plan → ExecutionContext.plan context ≡ plan
  knownPlan operation token before context raw plan observed decoded = sameRight
    (trans (sym (ExecutionContext.decoded context)) (trans (cong Plan.decode (knownRaw operation token before context raw observed)) decoded))

  data PendingCheck (operation : Text) (token : ℕ) (before : Store.World) : Set where
    blockedPending : Result → ¬ ExecutionContext operation token before → PendingCheck operation token before
    validPending : ExecutionContext operation token before → PendingCheck operation token before

  pendingDecision : ∀ {operation token before} → PendingCheck operation token before → ExecutionAdmission operation token before
  pendingDecision (blockedPending result _) = returned result
  pendingDecision (validPending context) = admitted context

  pendingAdmission : ∀ operation token before binding →
    Project.Registered.binding token (Store.OperationTables.bindings (Store.World.operations before)) ≡ just binding →
    Plan.textEqual (Store.BindingRow.operation binding) operation ≡ true → ExecutionAdmission operation token before
  checkPending : ∀ operation token before binding →
    Project.Registered.binding token (Store.OperationTables.bindings (Store.World.operations before)) ≡ just binding →
    Plan.textEqual (Store.BindingRow.operation binding) operation ≡ true → PendingCheck operation token before
  pendingAdmission operation token before binding foundBinding matchingExpected =
    pendingDecision (checkPending operation token before binding foundBinding matchingExpected)
  checkPending operation token before binding foundBinding matchingExpected with reservation token before in foundReservation
  ... | nothing = blockedPending unknownToken (λ context → noJust (trans (sym foundReservation) (ExecutionContext.originalReservation context)))
  ... | just reservedRow with Project.Registered.plan token (Store.OperationTables.plans (Store.World.operations before)) in foundPlan
  ... | nothing = blockedPending (needsRecovery binding) (λ context → noJust (trans (sym foundPlan) (ExecutionContext.originalPlan context)))
  ... | just raw with Plan.decode raw in decoded
  ... | inj₁ fault = blockedPending (inconsistent binding (malformedPlan fault)) (λ context → differentSummands
    (trans (sym (ExecutionContext.decoded context)) (trans (cong Plan.decode (knownRaw operation token before context raw foundPlan)) decoded)))
  ... | inj₂ plan with Plan.textEqual (Store.BindingRow.operation binding) (Plan.Saved.operation plan) in matching
  ... | false = blockedPending (inconsistent binding differentOperation) (λ context → falseTrue (trans (sym matching)
    (trans (sym (cong₂ (λ current stored → Plan.textEqual (Store.BindingRow.operation current) (Plan.Saved.operation stored))
      (sameJust (trans (sym (ExecutionContext.originalBinding context)) foundBinding)) (knownPlan operation token before context raw plan foundPlan decoded)))
      (ExecutionContext.matchingOperation context))))
  ... | true with Plan.executable library plan in executable
  ... | false = blockedPending (needsRecovery binding) (λ context → falseTrue (trans (sym executable)
    (trans (sym (cong (Plan.executable library) (knownPlan operation token before context raw plan foundPlan decoded))) (ExecutionContext.executable context))))
  ... | true with addressing? (Plan.Saved.steps plan)
  ... | no invalid = blockedPending (inconsistent binding invalidRegisteredPlan) (λ context → invalid
    (subst Addressing (cong Plan.Saved.steps (knownPlan operation token before context raw plan foundPlan decoded)) (ExecutionContext.addresses context)))
  ... | yes addresses with all? (λ declared → different? (Plan.Step.id declared) StoreStep.resultKey) (Plan.Saved.steps plan)
  ... | no invalid = blockedPending (inconsistent binding invalidRegisteredPlan) (λ context → invalid
    (subst (All (λ declared → Plan.Step.id declared ≢ StoreStep.resultKey))
      (cong Plan.Saved.steps (knownPlan operation token before context raw plan foundPlan decoded)) (ExecutionContext.separateResult context)))
  ... | yes separate with OpaqueJournal.check token before (Plan.Saved.steps plan) in checked
  ... | inj₁ fault = blockedPending (inconsistent binding undeclaredOrNonprefixAnswers) (λ context →
    OpaqueJournal.checkCannotFail token before _
      (subst (OpaqueJournal.Complete token before) (cong Plan.Saved.steps (knownPlan operation token before context raw plan foundPlan decoded)) (ExecutionContext.journal context)) fault checked)
  ... | inj₂ journal = validPending (executionContext reservedRow foundReservation binding foundBinding matchingExpected raw foundPlan plan decoded matching executable addresses separate journal)

  afterReadback : ∀ operation token before binding →
    Project.Registered.binding token (Store.OperationTables.bindings (Store.World.operations before)) ≡ just binding →
    Plan.textEqual (Store.BindingRow.operation binding) operation ≡ true → Result → ExecutionAdmission operation token before
  afterReadback operation token before binding foundBinding matching (pending _ _ _) = pendingAdmission operation token before binding foundBinding matching
  afterReadback operation token before binding foundBinding matching result@(completed _ _) = returned result
  afterReadback operation token before binding foundBinding matching result@(cancelled _ _ _) = returned result
  afterReadback operation token before binding foundBinding matching result@(inconsistent _ _) = returned result
  afterReadback operation token before binding foundBinding matching result@(needsRecovery _) = returned result
  afterReadback operation token before binding foundBinding matching result@(awaitingPlan _) = returned result
  afterReadback operation token before binding foundBinding matching result@(awaitingCompletion _) = returned result
  afterReadback operation token before binding foundBinding matching unknownToken = returned unknownToken
  afterReadback operation token before binding foundBinding matching reserved = returned reserved

  afterBinding : ∀ operation token before binding →
    Project.Registered.binding token (Store.OperationTables.bindings (Store.World.operations before)) ≡ just binding →
    ExecutionAdmission operation token before
  afterMatch : ∀ operation token before binding →
    Project.Registered.binding token (Store.OperationTables.bindings (Store.World.operations before)) ≡ just binding →
    (matched : Bool) → Plan.textEqual (Store.BindingRow.operation binding) operation ≡ matched → ExecutionAdmission operation token before
  afterBinding operation token before binding foundBinding =
    afterMatch operation token before binding foundBinding (Plan.textEqual (Store.BindingRow.operation binding) operation) refl
  afterMatch operation token before binding foundBinding false matching = returned (inconsistent binding differentOperation)
  afterMatch operation token before binding foundBinding true matching = afterReadback operation token before binding foundBinding matching (answer token before)

  admission : (operation : Text) → ∀ token before → ExecutionAdmission operation token before
  afterBindingLookup : ∀ operation token before observed → Project.Registered.binding token
    (Store.OperationTables.bindings (Store.World.operations before)) ≡ observed → ExecutionAdmission operation token before
  admission operation token before = afterBindingLookup operation token before
    (Project.Registered.binding token (Store.OperationTables.bindings (Store.World.operations before))) refl
  afterBindingLookup operation token before nothing found = returned (answer token before)
  afterBindingLookup operation token before (just binding) found = afterBinding operation token before binding found

  answerCompleted : ∀ token before binding raw plan value →
    Project.Registered.binding token (Store.OperationTables.bindings (Store.World.operations before)) ≡ just binding →
    Store.lookupCancellation before token ≡ nothing →
    Project.Registered.plan token (Store.OperationTables.plans (Store.World.operations before)) ≡ just raw →
    Plan.decode raw ≡ inj₂ plan → afterPlan binding plan (savedRows token before) ≡ completed binding value →
    answer token before ≡ completed binding value
  answerCompleted token before binding raw plan value original active saved decoded completedPlan
    rewrite original | active | saved | decoded | completedPlan = refl

  admissionCompleted : ∀ operation token before binding value →
    Project.Registered.binding token (Store.OperationTables.bindings (Store.World.operations before)) ≡ just binding →
    Plan.textEqual (Store.BindingRow.operation binding) operation ≡ true → answer token before ≡ completed binding value →
    admission operation token before ≡ returned (completed binding value)
  admissionCompleted operation token before binding value original matching completedOutcome
    = trans (alongObservation _ (afterBindingLookup operation token before) (just binding) original)
      (trans (alongObservation _ (afterMatch operation token before binding original) true matching)
        (cong (afterReadback operation token before binding original matching) completedOutcome))

  contextAfterNext : ∀ operation token before (context : ExecutionContext operation token before) next value changed →
    OpaqueJournal.next (OpaqueJournal.Complete.prefix (ExecutionContext.journal context)) ≡ just next →
    Store.World.operations changed ≡ Store.World.operations before →
    ExecutionContext operation token (Store.saveAnswer changed token (Plan.Step.id next) value)
  contextAfterNext operation token before context next value changed selected sameOperations = record
    { reservationRow = ExecutionContext.reservationRow context
    ; originalReservation = trans (cong (λ stored → Admission.reservation token (proj₁ stored)) registrationSame) (ExecutionContext.originalReservation context)
    ; bindingRow = ExecutionContext.bindingRow context
    ; originalBinding = trans (cong (λ stored → Project.Registered.binding token (proj₁ (proj₂ (proj₂ stored)))) registrationSame) (ExecutionContext.originalBinding context)
    ; requestedOperation = ExecutionContext.requestedOperation context
    ; rawPlan = ExecutionContext.rawPlan context
    ; originalPlan = trans (cong (λ stored → Project.Registered.plan token (proj₂ (proj₂ (proj₂ stored)))) registrationSame) (ExecutionContext.originalPlan context)
    ; plan = ExecutionContext.plan context
    ; decoded = ExecutionContext.decoded context
    ; matchingOperation = ExecutionContext.matchingOperation context
    ; executable = ExecutionContext.executable context
    ; addresses = ExecutionContext.addresses context
    ; separateResult = ExecutionContext.separateResult context
    ; journal = OpaqueJournal.extendComplete token changed _ relocated next value value
        (ExecutionContext.addresses context) (trans sameNext selected) refl }
    where
    relocation = OpaqueJournal.relocateComplete token before changed (Plan.Saved.steps (ExecutionContext.plan context)) sameOperations (ExecutionContext.journal context)
    relocated = proj₁ relocation
    sameNext = proj₂ relocation
    registrationSame : StoreStep.registration (Store.saveAnswer changed token (Plan.Step.id next) value) ≡ StoreStep.registration before
    registrationSame = trans (Store.savingAnswerPreservesOperationInputs changed token (Plan.Step.id next) value)
      (cong (λ tables → Store.OperationTables.reservations tables , Store.OperationTables.requestKeys tables ,
        Store.OperationTables.bindings tables , Store.OperationTables.plans tables) sameOperations)

  pendingAnswer : ∀ operation token before (context : ExecutionContext operation token before) next →
    OpaqueJournal.next (OpaqueJournal.Complete.prefix (ExecutionContext.journal context)) ≡ just next →
    Store.lookupCancellation before token ≡ nothing →
    Σ (List Store.SavedReplyRow) (λ receipts → answer token before ≡ pending (ExecutionContext.bindingRow context) next receipts)
  pendingAnswer operation token before context next selected active
    with pendingAfterPrefix token before (ExecutionContext.bindingRow context) (ExecutionContext.plan context) next
      (ExecutionContext.journal context) selected
      (undeclaredAbsent token before _ (ExecutionContext.journal context) StoreStep.resultKey (ExecutionContext.separateResult context))
      (ExecutionContext.matchingOperation context) (Plan.currentPlanRemainsReadable library (ExecutionContext.plan context) (ExecutionContext.executable context))
  ... | receipts , classified = receipts , observed
    where
    observed : answer token before ≡ pending (ExecutionContext.bindingRow context) next receipts
    observed rewrite ExecutionContext.originalBinding context | active | ExecutionContext.originalPlan context |
      ExecutionContext.decoded context | classified = refl

  pendingAdmissionExists : ∀ operation token before (context : ExecutionContext operation token before) →
    Σ (ExecutionContext operation token before) (λ actual → pendingAdmission operation token before
      (ExecutionContext.bindingRow context) (ExecutionContext.originalBinding context) (ExecutionContext.requestedOperation context) ≡ admitted actual)
  pendingAdmissionExists operation token before context with checkPending operation token before
    (ExecutionContext.bindingRow context) (ExecutionContext.originalBinding context) (ExecutionContext.requestedOperation context)
  ... | blockedPending result impossible = ⊥-elim (impossible context)
  ... | validPending actual = actual , refl

  admissionFromPending : ∀ operation token before (context : ExecutionContext operation token before) next receipts →
    answer token before ≡ pending (ExecutionContext.bindingRow context) next receipts →
    Σ (ExecutionContext operation token before) (λ actual → admission operation token before ≡ admitted actual)
  admissionFromPending operation token before context next receipts pendingOutcome
    with pendingAdmissionExists operation token before context
  ... | actual , admittedOutcome = actual , trans
    (alongObservation _ (afterBindingLookup operation token before) (just (ExecutionContext.bindingRow context)) (ExecutionContext.originalBinding context))
    (trans (alongObservation _ (afterMatch operation token before (ExecutionContext.bindingRow context) (ExecutionContext.originalBinding context)) true (ExecutionContext.requestedOperation context))
      (trans (cong (afterReadback operation token before (ExecutionContext.bindingRow context)
        (ExecutionContext.originalBinding context) (ExecutionContext.requestedOperation context)) pendingOutcome) admittedOutcome))

  preserveAfterNext : ∀ operation token before (context : ExecutionContext operation token before) first following rest value changed →
    OpaqueJournal.next (OpaqueJournal.Complete.prefix (ExecutionContext.journal context)) ≡ just first →
    OpaqueJournal.Cursor token before (Plan.Saved.steps (ExecutionContext.plan context)) (first ∷ following ∷ rest) →
    Store.lookupCancellation before token ≡ nothing → Store.World.operations changed ≡ Store.World.operations before →
    Σ (ExecutionContext operation token (Store.saveAnswer changed token (Plan.Step.id first) value))
      (λ actual → admission operation token (Store.saveAnswer changed token (Plan.Step.id first) value) ≡ admitted actual)
  preserveAfterNext operation token before context first following rest value changed selected cursor active sameOperations
    with OpaqueJournal.futureMissing token before _ first (following ∷ rest)
      (OpaqueJournal.Complete.prefix (ExecutionContext.journal context)) cursor selected
       | OpaqueJournal.cursorAddresses (ExecutionContext.addresses context) cursor
  ... | followingAbsent ∷ laterMissing | more (different ∷ distinct) addresses =
    admissionFromPending operation token after updated following (proj₁ pendingOutcome) (proj₂ pendingOutcome)
    where
    after = Store.saveAnswer changed token (Plan.Step.id first) value
    steps = Plan.Saved.steps (ExecutionContext.plan context)
    updated = contextAfterNext operation token before context first value changed selected sameOperations
    lookupChanged : ∀ key → Store.lookupSaved changed token key ≡ Store.lookupSaved before token key
    lookupChanged key = cong (λ tables → Store.lookupReply token key (Store.OperationTables.savedReplies tables)) sameOperations
    changedCursor = OpaqueJournal.transportCursor token before changed steps (first ∷ following ∷ rest)
      (λ key raw known → trans (lookupChanged key) known) cursor
    afterCursor = OpaqueJournal.transportCursor token changed after steps (first ∷ following ∷ rest)
      (λ key raw known → OpaqueJournal.publicationKeepsOldAnswer token (Plan.Step.id first) value value changed token key raw known) changedCursor
    firstReadable = OpaqueJournal.publicationReadable token (Plan.Step.id first) value value changed
      (trans (lookupChanged (Plan.Step.id first)) (OpaqueJournal.nextAbsent (OpaqueJournal.Complete.prefix (ExecutionContext.journal context)) first selected))
    nextCursor = OpaqueJournal.advanceCursor token after steps first (following ∷ rest) value afterCursor firstReadable
    followingStillAbsent = trans (Store.otherSavedAnswerPreserved changed token (Plan.Step.id first) value token (Plan.Step.id following)
      (λ same → different (sym (proj₂ same)))) (trans (lookupChanged (Plan.Step.id following)) followingAbsent)
    followingIsNext = OpaqueJournal.cursorNext token after steps following rest
      (OpaqueJournal.Complete.prefix (ExecutionContext.journal updated)) nextCursor followingStillAbsent
    stillActive = trans (Store.savingAnswerPreservesCancellation changed token (Plan.Step.id first) value token)
      (trans (cong (λ tables → Store.lookupCancellationRows token (Store.OperationTables.cancellations tables)) sameOperations) active)
    pendingOutcome = pendingAnswer operation token after updated following followingIsNext stillActive

  -- One final business transaction publishes its step answer and result
  -- together. This theorem concerns actual bindings/plans/rows and does not
  -- inspect the response payload or let a caller choose a successful goal.
  finalPairCompletes : ∀ operation token before (context : ExecutionContext operation token before) last value changed →
    OpaqueJournal.next (OpaqueJournal.Complete.prefix (ExecutionContext.journal context)) ≡ just last →
    OpaqueJournal.Cursor token before (Plan.Saved.steps (ExecutionContext.plan context)) (last ∷ []) →
    Store.lookupSaved before token StoreStep.resultKey ≡ nothing → Store.lookupCancellation before token ≡ nothing →
    Store.World.operations changed ≡ Store.World.operations before →
    admission operation token (Store.saveAnswer (Store.saveAnswer changed token (Plan.Step.id last) value) token StoreStep.resultKey value) ≡
      returned (completed (ExecutionContext.bindingRow context) value)
  finalPairCompletes operation token before context last value changed selected cursor absent active sameOperations
    with OpaqueJournal.relocateComplete token before changed (Plan.Saved.steps (ExecutionContext.plan context)) sameOperations (ExecutionContext.journal context)
  ... | relocated , sameNext = admissionCompleted operation token final binding value bindingReadable
    (ExecutionContext.requestedOperation context)
    (answerCompleted token final binding (ExecutionContext.rawPlan context) plan value bindingReadable cancellationReadable planReadable
      (ExecutionContext.decoded context) completedPlan)
    where
    plan = ExecutionContext.plan context
    binding = ExecutionContext.bindingRow context
    steps = Plan.Saved.steps plan
    chosen = trans sameNext selected
    stepWorld = Store.saveAnswer changed token (Plan.Step.id last) value
    final = Store.saveAnswer stepWorld token StoreStep.resultKey value
    lookupChanged : ∀ key → Store.lookupSaved changed token key ≡ Store.lookupSaved before token key
    lookupChanged key = cong (λ tables → Store.lookupReply token key (Store.OperationTables.savedReplies tables)) sameOperations
    absentStep = OpaqueJournal.nextAbsent (OpaqueJournal.Complete.prefix relocated) last chosen
    journal = OpaqueJournal.extendComplete token changed steps relocated last value value (ExecutionContext.addresses context) chosen refl
    cursorChanged = OpaqueJournal.transportCursor token before changed steps (last ∷ [])
      (λ key raw known → trans (lookupChanged key) known) cursor
    cursorStep = OpaqueJournal.transportCursor token changed stepWorld steps (last ∷ [])
      (λ key raw known → OpaqueJournal.publicationKeepsOldAnswer token (Plan.Step.id last) value value changed token key raw known) cursorChanged
    stepReadable = OpaqueJournal.publicationReadable token (Plan.Step.id last) value value changed absentStep
    end = OpaqueJournal.advanceCursor token stepWorld steps last [] value cursorStep stepReadable
    finished = OpaqueJournal.cursorFinished token stepWorld steps (OpaqueJournal.Complete.prefix journal) end
    lastIsNotResult = OpaqueJournal.nextProperty (λ declared → Plan.Step.id declared ≢ StoreStep.resultKey)
      (OpaqueJournal.Complete.prefix (ExecutionContext.journal context)) (ExecutionContext.separateResult context) last selected
    noResult = trans (Store.otherSavedAnswerPreserved changed token (Plan.Step.id last) value token StoreStep.resultKey
      (λ same → lastIsNotResult (sym (proj₂ same)))) (trans (lookupChanged StoreStep.resultKey) absent)
    completedPlan = completedAfterResult token stepWorld binding plan value journal finished (ExecutionContext.separateResult context)
      noResult (ExecutionContext.matchingOperation context) (Plan.currentPlanRemainsReadable library plan (ExecutionContext.executable context))
    registrationSame : StoreStep.registration final ≡ StoreStep.registration before
    registrationSame = trans (Store.savingAnswerPreservesOperationInputs stepWorld token StoreStep.resultKey value)
      (trans (Store.savingAnswerPreservesOperationInputs changed token (Plan.Step.id last) value)
        (cong (λ tables → Store.OperationTables.reservations tables , Store.OperationTables.requestKeys tables ,
          Store.OperationTables.bindings tables , Store.OperationTables.plans tables) sameOperations))
    bindingReadable = trans (cong (λ stored → Project.Registered.binding token (proj₁ (proj₂ (proj₂ stored)))) registrationSame)
      (ExecutionContext.originalBinding context)
    planReadable = trans (cong (λ stored → Project.Registered.plan token (proj₂ (proj₂ (proj₂ stored)))) registrationSame)
      (ExecutionContext.originalPlan context)
    cancellationReadable = trans (Store.savingAnswerPreservesCancellation stepWorld token StoreStep.resultKey value token)
      (trans (Store.savingAnswerPreservesCancellation changed token (Plan.Step.id last) value token)
        (trans (cong (λ tables → Store.lookupCancellationRows token (Store.OperationTables.cancellations tables)) sameOperations) active))

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
