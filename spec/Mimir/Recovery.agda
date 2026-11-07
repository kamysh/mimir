{-# OPTIONS --safe #-}
-- The recovery goal is fixed here, outside operation implementations. Neither
-- an alternative predicate nor an operation-chosen observation is a field.
module Mimir.Recovery where

open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-assoc; ++-identityʳ; map-++)
open import Data.List.Relation.Unary.Any using (Any)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
import Mimir.ApplicationStore as Store
import Mimir.StructuredValue as Wire
import Mimir.Effects as Effects
import Mimir.DatabaseTransaction as Database
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Unit using (⊤; tt)

-- Assembly fixes World once for the entire dispatcher. An operation over a
-- smaller world cannot be supplied where this dispatcher expects the larger
-- one. The observation retains the WHOLE world and the complete semantic reply.
module Over (World : Set) where
  Observation = World × Wire.Value

  observe : World → Wire.Value → Observation
  observe state reply = state , reply

  record Intent (Input : Set) : Set where
    field
      intended : Input → World → World
      expectedReply : Input → World → Wire.Value

  record Invocation (Input : Set) : Set where
    constructor invocation
    field
      input : Input
      initial : World

  expected : ∀ {Input} → Intent Input → Invocation Input → Observation
  expected intent call = observe
    (Intent.intended intent (Invocation.input call) (Invocation.initial call))
    (Intent.expectedReply intent (Invocation.input call) (Invocation.initial call))

  Goal : ∀ {Input} → Intent Input → Invocation Input → World → Wire.Value → Set
  Goal intent call final reply = observe final reply ≡ expected intent call

  -- Both conclusions use the same original invocation. A retry cannot change
  -- either the starting world or its expected reply to make its result pass.
  goalDeterminesStateAndReply : ∀ {Input} (intent : Intent Input) call
    firstState firstReply secondState secondReply →
    Goal intent call firstState firstReply → Goal intent call secondState secondReply →
    firstState ≡ secondState × firstReply ≡ secondReply
  goalDeterminesStateAndReply intent call firstState firstReply secondState secondReply first second =
    cong proj₁ same , cong proj₂ same
    where same = trans first (sym second)

-- Concrete application operations share every represented store component:
-- graph and learning history, document chunks, BOTH vector tables and grounds.
-- This alias is chosen by application assembly, not by each operation.
module Business = Over Store.World

-- Atomic supplies the application's physical meaning for one effect and its
-- reply. A control transcript by itself is not a physical execution witness.
module Execution (World Effect : Set) (Reply : Effect → Set)
  (Atomic : World → (effect : Effect) → Reply effect → World → Set) where
  module E = Effects.Protocol Effect Reply

  data Changes : World → List E.Event → World → Set where
    unchanged : ∀ state → Changes state [] state
    changed : ∀ before effect reply middle {events after} →
      Atomic before effect reply middle → Changes middle events after →
      Changes before ((effect , reply) ∷ events) after

  record Completed {Result : Set} (script : E.Script Result)
    (before after : World) (result : Result) : Set where
    constructor completed
    field
      events : List E.Event
      returned : E.Runs script events result
      changes : Changes before events after

  data Interrupted {Result : Set} (script : E.Script Result)
    (before : World) : World → Set where
    -- Includes before the first effect, after any observed reply, and after
    -- the script finished but its caller did not receive the final result.
    atPrefix : ∀ events residual current → E.Prefix script events residual →
      Changes before events current → Interrupted script before current
    -- The active statement may have finished before its reply was delivered.
    -- Its physical change is retained; its reply is NOT an observed event.
    beforeReply : ∀ events effect continuation current reply after →
      E.Prefix script events (E.ask effect continuation) →
      Changes before events current → Atomic current effect reply after →
      Interrupted script before after

  private
    runPrefix : ∀ {Result} {script : E.Script Result} {events result} →
      E.Runs script events result → E.Prefix script events (E.done result)
    runPrefix (E.returned result) = E.stopped (E.done result)
    runPrefix (E.replied effect continuation reply rest) =
      E.replied effect continuation reply (runPrefix rest)

  completedRunMayLoseFinalReply : ∀ {Result} (script : E.Script Result)
    before after result → Completed script before after result →
    Interrupted script before after
  completedRunMayLoseFinalReply script before after result
    (completed events execution changes) =
    atPrefix events (E.done result) after (runPrefix execution) changes

-- Committed database statements use the existing PostgreSQL atomicity
-- dependency directly. No new rollback or acknowledgement assumptions appear.
module Transactions (World Statement : Set) (proposed : Statement → World → World) where
  Reply : Statement → Set
  Reply _ = Database.Receipt

  Atomic : World → Statement → Database.Receipt → World → Set
  Atomic before statement receipt after =
    Database.Atomic before (proposed statement before) receipt after

  module X = Execution World Statement Reply Atomic

  lostAcknowledgementIncludesBothWorlds : ∀ {Result} statement
    (continuation : Reply statement → X.E.Script Result) before →
    X.Interrupted (X.E.ask statement continuation) before before ×
    X.Interrupted (X.E.ask statement continuation) before (proposed statement before)
  lostAcknowledgementIncludesBothWorlds statement continuation before =
    X.beforeReply [] statement continuation before Database.acknowledgementLost before
      (X.E.stopped _) (X.unchanged before) Database.unknownBefore ,
    X.beforeReply [] statement continuation before Database.acknowledgementLost (proposed statement before)
      (X.E.stopped _) (X.unchanged before) Database.unknownAfter

-- There is no Goal, Completed, valid-input or readiness predicate to replace.
-- Inputs are the operation's admitted inputs; every one owes a lawful complete
-- execution from every represented starting world, as well as retry safety.
record Recoverable (World Input : Set) : Set₁ where
  field
    Effect : Set
    Reply : Effect → Set
  module E = Effects.Protocol Effect Reply
  field
    script : Input → E.Script Wire.Value
    Atomic : World → (effect : Effect) → Reply effect → World → Set
    intent : Over.Intent World Input
  module X = Execution World Effect Reply Atomic
  module G = Over World
  field
    converges : ∀ input initial interrupted final reply →
      X.Interrupted (script input) initial interrupted →
      X.Completed (script input) interrupted final reply →
      G.Goal intent (G.invocation input initial) final reply
    progress : ∀ input initial →
      Σ World (λ final → Σ Wire.Value (λ reply →
        X.Completed (script input) initial final reply))

  -- Ordinary completion is also checked: interrupting before the first effect
  -- leaves the initial world intact, so convergence applies to that execution.
  completedMeetsIntent : ∀ input initial final reply →
    X.Completed (script input) initial final reply →
    G.Goal intent (G.invocation input initial) final reply
  completedMeetsIntent input initial final reply execution =
    converges input initial initial final reply
      (X.atPrefix [] (script input) initial (E.stopped _) (X.unchanged initial))
      execution

  progressReachesIntent : ∀ input initial →
    Σ World (λ final → Σ Wire.Value (λ reply →
      X.Completed (script input) initial final reply ×
      G.Goal intent (G.invocation input initial) final reply))
  progressReachesIntent input initial with progress input initial
  ... | final , reply , execution =
    final , reply , execution , completedMeetsIntent input initial final reply execution

-- One committed statement is not automatically repeatable. Its physical
-- meaning and independently reviewed intent are separate, and the complete
-- observation (including the reply) must be stable on replay.
module Single where
  record Statement (World Input : Set) : Set where
    field
      execute : Input → World → World × Wire.Value
      intent : Over.Intent World Input
      correct : ∀ input initial → execute input initial ≡
        Over.expected World intent (Over.invocation input initial)

  record Idempotent {World Input} (statement : Statement World Input) : Set where
    field
      stable : ∀ input initial →
        Statement.execute statement input (proj₁ (Statement.execute statement input initial)) ≡
        Statement.execute statement input initial

  module Semantics {World Input} (statement : Statement World Input) where
    execute = Statement.execute statement
    module G = Over World

    -- Only a confirmed statement supplies a completed reply. Aborts and lost
    -- acknowledgements remain interruption states, covered below directly
    -- from every constructor of the existing PostgreSQL atomicity contract.
    Atomic : World → Input → Wire.Value → World → Set
    Atomic before input reply after =
      Database.Atomic before (proj₁ (execute input before)) Database.committed after ×
      reply ≡ proj₂ (execute input before)

    module X = Execution World Input (λ _ → Wire.Value) Atomic
    module E = X.E

    script : Input → E.Script Wire.Value
    script input = E.ask input E.done

    oneObservation : ∀ input before after reply →
      X.Changes before ((input , reply) ∷ []) after →
      G.observe after reply ≡ execute input before
    oneObservation input before after reply
      (X.changed _ _ _ _ (Database.committedAll , refl) (X.unchanged _)) = refl

    completedObservation : ∀ input before after reply →
      X.Completed (script input) before after reply →
      G.observe after reply ≡ execute input before
    completedObservation input before after reply
      (X.completed _ (E.replied _ _ _ (E.returned _)) physical) =
      oneObservation input before after reply physical

    interruptionState : ∀ input initial interrupted →
      X.Interrupted (script input) initial interrupted →
      interrupted ≡ initial ⊎ interrupted ≡ proj₁ (execute input initial)
    interruptionState input initial interrupted
      (X.atPrefix _ _ _ (E.stopped _) (X.unchanged _)) = inj₁ refl
    interruptionState input initial interrupted
      (X.atPrefix _ _ _ (E.replied _ _ _ (E.stopped _)) physical) =
      inj₂ (cong proj₁ (oneObservation input initial interrupted _ physical))
    interruptionState input initial interrupted
      (X.beforeReply _ _ _ _ _ _ (E.stopped _) (X.unchanged _)
        (Database.committedAll , refl)) = inj₂ refl
    interruptionState input initial interrupted
      (X.beforeReply _ _ _ _ _ _ (E.replied _ _ _ ()) physical active)

    everyDatabaseReceiptCovered : ∀ input initial receipt interrupted →
      Database.Atomic initial (proj₁ (execute input initial)) receipt interrupted →
      X.Interrupted (script input) initial interrupted
    everyDatabaseReceiptCovered input initial .Database.committed _ Database.committedAll =
      X.beforeReply [] input E.done initial (proj₂ (execute input initial)) _
        (E.stopped _) (X.unchanged initial) (Database.committedAll , refl)
    everyDatabaseReceiptCovered input initial .Database.aborted _ Database.abortedNone =
      X.atPrefix [] (script input) initial (E.stopped _) (X.unchanged initial)
    everyDatabaseReceiptCovered input initial .Database.acknowledgementLost _ Database.unknownBefore =
      X.atPrefix [] (script input) initial (E.stopped _) (X.unchanged initial)
    everyDatabaseReceiptCovered input initial .Database.acknowledgementLost _ Database.unknownAfter =
      X.beforeReply [] input E.done initial (proj₂ (execute input initial)) _
        (E.stopped _) (X.unchanged initial) (Database.committedAll , refl)

    converges : Idempotent statement → ∀ input initial interrupted final reply →
      X.Interrupted (script input) initial interrupted →
      X.Completed (script input) interrupted final reply →
      G.Goal (Statement.intent statement) (G.invocation input initial) final reply
    converges repeatable input initial interrupted final reply interruption completion
      with interruptionState input initial interrupted interruption
    ... | inj₁ beforeEquality = trans (completedObservation input interrupted final reply completion)
      (trans (cong (execute input) beforeEquality) (Statement.correct statement input initial))
    ... | inj₂ afterEquality = trans (completedObservation input interrupted final reply completion)
      (trans (cong (execute input) afterEquality)
        (trans (Idempotent.stable repeatable input initial) (Statement.correct statement input initial)))

    progress : ∀ input initial → Σ World (λ final → Σ Wire.Value (λ reply →
      X.Completed (script input) initial final reply))
    progress input initial = proj₁ (execute input initial) , proj₂ (execute input initial) ,
      X.completed ((input , proj₂ (execute input initial)) ∷ [])
        (E.replied input E.done (proj₂ (execute input initial)) (E.returned _))
        (X.changed initial input _ _ (Database.committedAll , refl) (X.unchanged _))

  single : ∀ {World Input} (statement : Statement World Input) →
    Idempotent statement → Recoverable World Input
  single {Input = Input} statement repeatable = record
    { Effect = Input
    ; Reply = λ _ → Wire.Value
    ; script = S.script
    ; Atomic = S.Atomic
    ; intent = Statement.intent statement
    ; converges = S.converges repeatable
    ; progress = S.progress
    }
    where module S = Semantics statement

  readStatement : ∀ {World Input} → (Input → World → Wire.Value) → Statement World Input
  readStatement answer = record
    { execute = λ input initial → initial , answer input initial
    ; intent = record { intended = λ _ initial → initial; expectedReply = answer }
    ; correct = λ _ _ → refl
    }

  readIsIdempotent : ∀ {World Input} (answer : Input → World → Wire.Value) →
    Idempotent (readStatement answer)
  readIsIdempotent answer = record { stable = λ _ _ → refl }

  replyMustRepeat : ∀ {World Input} (statement : Statement World Input) →
    Idempotent statement → ∀ input initial →
    proj₂ (Statement.execute statement input (proj₁ (Statement.execute statement input initial))) ≡
    proj₂ (Statement.execute statement input initial)
  replyMustRepeat statement repeatable input initial =
    cong proj₂ (Idempotent.stable repeatable input initial)

-- Reservation metadata is separate from business publication. Identities and
-- timestamps are supplied by PostgreSQL; this module has no identity generator
-- or uniqueness proposition. The database primary-key/default contracts apply.
module Reservations (Business Identity Timestamp : Set)
  (_≟_ : (first second : Identity) → Dec (first ≡ second)) where

  record Entry : Set where
    constructor entry
    field token : Identity; reservedAt : Timestamp

  record State : Set where
    constructor state
    field business : Business; entries : List Entry

  publish : State → Entry → State
  publish before allocated = state (State.business before) (allocated ∷ State.entries before)

  find : Identity → List Entry → Maybe Entry
  find token [] = nothing
  find token (allocated ∷ rest) with token ≟ Entry.token allocated
  ... | yes _ = just allocated
  ... | no _ = find token rest

  readBack : State → Identity → Maybe Entry
  readBack before token = find token (State.entries before)

  allocatedTokenIsReadable : ∀ before allocated →
    readBack (publish before allocated) (Entry.token allocated) ≡ just allocated
  allocatedTokenIsReadable before allocated with Entry.token allocated ≟ Entry.token allocated
  ... | yes _ = refl
  ... | no impossible = ⊥-elim (impossible refl)

  businessUnchangedForEveryReceipt : ∀ before allocated receipt after →
    Database.Atomic before (publish before allocated) receipt after →
    State.business after ≡ State.business before
  businessUnchangedForEveryReceipt before allocated receipt after publication =
    Database.invariantPreserved (λ current → State.business current ≡ State.business before)
      publication refl refl

-- This is the state selected by one reserved token. Request includes the
-- admitted operation, arguments and relevant settings; equality is PostgreSQL
-- JSONB equality. Timestamp allocation is an external database observation.
-- Other tokens and all business data are carried intact in Business.
module Bindings (Business Request Timestamp : Set)
  (_≟_ : (first second : Request) → Dec (first ≡ second)) where

  record Entry : Set where
    constructor entry
    field request : Request; boundAt : Timestamp

  record State : Set where
    constructor state
    field business : Business; reserved : Bool; binding : Maybe Entry

  data Reply : Set where
    unknownToken : Reply
    bound changedRequest : Entry → Reply

  proposed : State → Entry → State
  proposed before requested with State.reserved before | State.binding before
  ... | true | nothing = record before { binding = just requested }
  ... | _ | _ = before

  reply : State → Entry → Reply
  reply before requested with State.reserved before | State.binding before
  ... | false | _ = unknownToken
  ... | true | nothing = bound requested
  ... | true | just original with Entry.request requested ≟ Entry.request original
  ...   | yes _ = bound original
  ...   | no _ = changedRequest original

  existingBindingPreserved : ∀ before requested original → State.binding before ≡ just original →
    State.binding (proposed before requested) ≡ just original
  existingBindingPreserved (state business false binding) requested original existing = existing
  existingBindingPreserved (state business true nothing) requested original ()
  existingBindingPreserved (state business true (just previous)) requested original existing = existing

  everyReceiptPreservesExistingBinding : ∀ before requested original receipt after →
    State.binding before ≡ just original →
    Database.Atomic before (proposed before requested) receipt after →
    State.binding after ≡ just original
  everyReceiptPreservesExistingBinding before requested original receipt after existing publication =
    Database.invariantPreserved (λ current → State.binding current ≡ just original) publication
      existing (existingBindingPreserved before requested original existing)

  proposedPreservesBusiness : ∀ before requested → State.business (proposed before requested) ≡ State.business before
  proposedPreservesBusiness (state business false binding) requested = refl
  proposedPreservesBusiness (state business true nothing) requested = refl
  proposedPreservesBusiness (state business true (just original)) requested = refl

  everyReceiptPreservesBusiness : ∀ before requested receipt after →
    Database.Atomic before (proposed before requested) receipt after → State.business after ≡ State.business before
  everyReceiptPreservesBusiness before requested receipt after publication =
    Database.invariantPreserved (λ current → State.business current ≡ State.business before) publication
      refl (proposedPreservesBusiness before requested)

  retryCannotReplaceRequest : ∀ business original requested →
    proposed (state business true (just original)) requested ≡ state business true (just original)
  retryCannotReplaceRequest business original requested = refl

  retryProposalIsStable : ∀ before first retry →
    proposed (proposed before first) retry ≡ proposed before first
  retryProposalIsStable (state business false binding) first retry = refl
  retryProposalIsStable (state business true nothing) first retry = refl
  retryProposalIsStable (state business true (just original)) first retry = refl

  changedRequestReturnsOriginal : ∀ business original requested →
    (Entry.request requested ≡ Entry.request original → Data.Empty.⊥) →
    reply (state business true (just original)) requested ≡ changedRequest original
  changedRequestReturnsOriginal business original requested different
    with Entry.request requested ≟ Entry.request original
  ... | yes same = ⊥-elim (different same)
  ... | no _ = refl

  sameRequestReturnsOriginal : ∀ business original requested →
    Entry.request requested ≡ Entry.request original →
    reply (state business true (just original)) requested ≡ bound original
  sameRequestReturnsOriginal business original requested same
    with Entry.request requested ≟ Entry.request original
  ... | yes _ = refl
  ... | no different = ⊥-elim (different same)

-- One named step after its request binding has been checked under the token
-- lock. Business retains the complete surrounding world, including other
-- tokens and steps. The selected reply is published with the business change.
module SavedStep (Business Input : Set)
  (apply : Input → Business → Business × Wire.Value) where

  record State : Set where
    constructor state
    field business : Business; savedReply : Maybe Wire.Value

  execute : Input → State → State × Wire.Value
  execute input (state business (just saved)) = state business (just saved) , saved
  execute input (state business nothing) with apply input business
  ... | changed , reply = state changed (just reply) , reply

  replayUsesOriginalReply : ∀ input business saved →
    execute input (state business (just saved)) ≡ (state business (just saved) , saved)
  replayUsesOriginalReply input business saved = refl

  stable : ∀ input initial →
    execute input (proj₁ (execute input initial)) ≡ execute input initial
  stable input (state business (just saved)) = refl
  stable input (state business nothing) with apply input business
  ... | changed , reply = refl

  -- The caller still owes the independent intended outcome over the WHOLE
  -- State. Saving an answer does not prove that the business change is right.
  statement : (intent : Over.Intent State Input) →
    (∀ input initial → execute input initial ≡ Over.expected State intent (Over.invocation input initial)) →
    Single.Statement State Input
  statement intent correct = record { execute = execute ; intent = intent ; correct = correct }

  recoverable : (intent : Over.Intent State Input) →
    (∀ input initial → execute input initial ≡ Over.expected State intent (Over.invocation input initial)) →
    Recoverable State Input
  recoverable intent correct = Single.single (statement intent correct) (record { stable = stable })

  rollbackPreservesBusinessAndReply : ∀ input before after →
    Database.Atomic before (proj₁ (execute input before)) Database.aborted after → after ≡ before
  rollbackPreservesBusinessAndReply input before .before Database.abortedNone = refl

-- Checked journal views retain the original plan and an exact completed
-- prefix. A missing or out-of-order row cannot produce this checked view.
module PlanOrder (Business Key : Set) where
  record State : Set where
    constructor state
    field business : Business
          planned completed remaining : List Key
          partition : planned ≡ completed ++ remaining

  capture : Business → List Key → State
  capture business keys = state business keys [] keys refl

  capturePreservesBusiness : ∀ business keys → State.business (capture business keys) ≡ business
  capturePreservesBusiness business keys = refl

  data Step : State → Key → State → Set where
    publish : ∀ business planned completed key rest partition updated →
      Step (state business planned completed (key ∷ rest) partition) key
        (state updated planned (completed ++ (key ∷ [])) rest
          (trans partition (sym (++-assoc completed (key ∷ []) rest))))
    replay : ∀ current key → Any (_≡ key) (State.completed current) → Step current key current

  planNeverChanges : ∀ before key after → Step before key after → State.planned after ≡ State.planned before
  planNeverChanges before key after (publish business planned completed .key rest partition updated) = refl
  planNeverChanges before key .before (replay .before .key saved) = refl

  newStepMustBeNext : ∀ before key after → Step before key after →
    (Any (_≡ key) (State.completed before) → Data.Empty.⊥) →
    Σ (List Key) (λ rest → State.remaining before ≡ key ∷ rest)
  newStepMustBeNext before key after (publish business planned completed .key rest partition updated) absent = rest , refl
  newStepMustBeNext before key .before (replay .before .key saved) absent = ⊥-elim (absent saved)

  nextStepIsAvailable : ∀ business planned completed key rest partition updated →
    Σ State (λ after → Step (state business planned completed (key ∷ rest) partition) key after)
  nextStepIsAvailable business planned completed key rest partition updated =
    _ , publish business planned completed key rest partition updated

  record Finished (current : State) : Set where
    constructor finished
    field nothingRemaining : State.remaining current ≡ []

  completionRequiresEveryPlannedStep : ∀ current → Finished current → State.completed current ≡ State.planned current
  completionRequiresEveryPlannedStep current (finished empty) = sym
    (trans (State.partition current)
      (trans (cong (State.completed current ++_) empty) (++-identityʳ (State.completed current))))

-- The final business change, last step answer and whole-operation answer are
-- one database publication. Neither answer may be inferred from data alone.
module FinalPublication (Business : Set) where
  record Answers : Set where
    constructor answers
    field stepReply operationReply : Wire.Value

  record State : Set where
    constructor state
    field business : Business; saved : Maybe Answers

  publish : Business → Answers → State
  publish changed replies = state changed (just replies)

  everyReceiptKeepsPublicationTogether : ∀ before changed replies receipt after →
    Database.Atomic before (publish changed replies) receipt after →
    after ≡ before ⊎ after ≡ publish changed replies
  everyReceiptKeepsPublicationTogether before changed replies .Database.committed .(publish changed replies) Database.committedAll = inj₂ refl
  everyReceiptKeepsPublicationTogether before changed replies .Database.aborted .before Database.abortedNone = inj₁ refl
  everyReceiptKeepsPublicationTogether before changed replies .Database.acknowledgementLost .before Database.unknownBefore = inj₁ refl
  everyReceiptKeepsPublicationTogether before changed replies .Database.acknowledgementLost .(publish changed replies) Database.unknownAfter = inj₂ refl

  completedReadbackHasBothAnswers : ∀ changed replies →
    State.saved (publish changed replies) ≡ just replies ×
    State.business (publish changed replies) ≡ changed
  completedReadbackHasBothAnswers changed replies = refl , refl

  -- Re-reading a completed operation does not accept a newly supplied answer.
  readBack : State → Maybe Answers
  readBack = State.saved

  readBackRetainsOriginal : ∀ changed stepReply operationReply →
    readBack (publish changed (answers stepReply operationReply)) ≡
      just (answers stepReply operationReply)
  readBackRetainsOriginal changed stepReply operationReply = refl

-- A checked, frozen plan is read before execution. Its completed entries carry
-- the original answers; only remaining entries can change business data. The
-- final business step also saves completion, as required by the core writer.
module SavedSequence (Business Action : Set)
  (apply : Action → Business → Business × Wire.Value)
  (finish : List (Action × Wire.Value) → Wire.Value) where

  data State : Set where
    active : Business → List (Action × Wire.Value) → List Action → State
    finished : Business → List (Action × Wire.Value) → State

  afterWrite : Business → List (Action × Wire.Value) → List Action → State
  afterWrite business saved [] = finished business saved
  afterWrite business saved remaining@(_ ∷ _) = active business saved remaining

  planned : State → List Action
  planned (active business saved remaining) = map proj₁ saved ++ remaining
  planned (finished business saved) = map proj₁ saved

  planAfterWrite : ∀ business saved remaining → planned (afterWrite business saved remaining) ≡ map proj₁ saved ++ remaining
  planAfterWrite business saved [] = sym (++-identityʳ (map proj₁ saved))
  planAfterWrite business saved (_ ∷ _) = refl

  advance : State → State
  advance (finished business saved) = finished business saved
  advance (active business saved []) = finished business saved
  advance (active business saved (action ∷ rest)) =
    afterWrite (proj₁ (apply action business)) (saved ++ ((action , proj₂ (apply action business)) ∷ [])) rest

  planNeverChanges : ∀ current → planned (advance current) ≡ planned current
  planNeverChanges (finished business saved) = refl
  planNeverChanges (active business saved []) = sym (++-identityʳ (map proj₁ saved))
  planNeverChanges (active business saved (action ∷ rest)) with apply action business
  ... | changed , answer = trans (planAfterWrite changed (saved ++ ((action , answer) ∷ [])) rest)
    (trans (cong (_++ rest) (map-++ proj₁ saved ((action , answer) ∷ [])))
      (++-assoc (map proj₁ saved) (action ∷ []) rest))

  -- This evaluator is operational semantics, NOT an operation's intent. The
  -- recovery constructor below separately requires equality to reviewed intent.
  normalizePending : Business → List (Action × Wire.Value) → List Action → State × Wire.Value
  normalizePending business saved [] = finished business saved , finish saved
  normalizePending business saved (action ∷ rest) with apply action business
  ... | changed , answer = normalizePending changed (saved ++ ((action , answer) ∷ [])) rest

  normalize : State → State × Wire.Value
  normalize (finished business saved) = finished business saved , finish saved
  normalize (active business saved remaining) = normalizePending business saved remaining

  normalizeAfterWrite : ∀ business saved remaining → normalize (afterWrite business saved remaining) ≡ normalizePending business saved remaining
  normalizeAfterWrite business saved [] = refl
  normalizeAfterWrite business saved (_ ∷ _) = refl

  advancePreservesOutcome : ∀ current → normalize (advance current) ≡ normalize current
  advancePreservesOutcome (finished business saved) = refl
  advancePreservesOutcome (active business saved []) = refl
  advancePreservesOutcome (active business saved (action ∷ rest)) with apply action business
  ... | changed , answer = normalizeAfterWrite changed (saved ++ ((action , answer) ∷ [])) rest

  data Effect : Set where
    inspect : Effect
    publish : State → Effect

  Reply : Effect → Set
  Reply inspect = State
  Reply (publish current) = ⊤

  -- Successful receipts continue the run. Aborts and lost acknowledgements
  -- are interruptions, covered by everyReceiptAtEveryWriteBoundary below.
  data Atomic : State → (effect : Effect) → Reply effect → State → Set where
    inspected : ∀ current → Atomic current inspect current current
    published : ∀ current after → Database.Atomic current (advance current) Database.committed after →
      Atomic current (publish current) tt after

  module X = Execution State Effect Reply Atomic
  module E = X.E
  module G = Over State

  mutual
    runPending : Business → List (Action × Wire.Value) → List Action → E.Script Wire.Value
    runPending business saved [] = E.ask (publish (active business saved [])) (λ _ → E.done (finish saved))
    runPending business saved (action ∷ rest) with apply action business
    ... | changed , answer = E.ask (publish (active business saved (action ∷ rest)))
      (λ _ → runTail changed (saved ++ ((action , answer) ∷ [])) rest)

    runTail : Business → List (Action × Wire.Value) → List Action → E.Script Wire.Value
    runTail business saved [] = E.done (finish saved)
    runTail business saved remaining@(_ ∷ _) = runPending business saved remaining

  runFromState : State → E.Script Wire.Value
  runFromState (finished business saved) = E.done (finish saved)
  runFromState (active business saved remaining) = runPending business saved remaining

  start : ⊤ → E.Script Wire.Value
  start _ = E.ask inspect runFromState

  atomicPreservesOutcome : ∀ before effect reply after → Atomic before effect reply after →
    normalize after ≡ normalize before
  atomicPreservesOutcome current .inspect .current .current (inspected .current) = refl
  atomicPreservesOutcome current .(publish current) .tt .(advance current)
    (published .current .(advance current) Database.committedAll) = advancePreservesOutcome current

  changesPreserveOutcome : ∀ before events after → X.Changes before events after → normalize after ≡ normalize before
  changesPreserveOutcome before .[] .before (X.unchanged .before) = refl
  changesPreserveOutcome before _ after
    (X.changed .before effect reply middle {events = events} publication physical) =
    trans (changesPreserveOutcome middle events after physical)
      (atomicPreservesOutcome before effect reply middle publication)

  interruptionsPreserveOutcome : ∀ initial interrupted → X.Interrupted (start tt) initial interrupted →
    normalize interrupted ≡ normalize initial
  interruptionsPreserveOutcome initial interrupted (X.atPrefix events residual .interrupted prefix physical) =
    changesPreserveOutcome initial events interrupted physical
  interruptionsPreserveOutcome initial interrupted
    (X.beforeReply events effect continuation current reply .interrupted prefix physical publication) =
    trans (atomicPreservesOutcome current effect reply interrupted publication)
      (changesPreserveOutcome initial events current physical)

  everyReceiptAtEveryWriteBoundary : ∀ initial events current continuation receipt actual →
    E.Prefix (start tt) events (E.ask (publish current) continuation) →
    X.Changes initial events current → Database.Atomic current (advance current) receipt actual →
    X.Interrupted (start tt) initial actual
  everyReceiptAtEveryWriteBoundary initial events current continuation .Database.committed .(advance current)
    prefix physical Database.committedAll =
    X.beforeReply events (publish current) continuation current tt (advance current) prefix physical
      (published current (advance current) Database.committedAll)
  everyReceiptAtEveryWriteBoundary initial events current continuation .Database.aborted .current
    prefix physical Database.abortedNone = X.atPrefix events _ current prefix physical
  everyReceiptAtEveryWriteBoundary initial events current continuation .Database.acknowledgementLost .current
    prefix physical Database.unknownBefore = X.atPrefix events _ current prefix physical
  everyReceiptAtEveryWriteBoundary initial events current continuation .Database.acknowledgementLost .(advance current)
    prefix physical Database.unknownAfter =
    X.beforeReply events (publish current) continuation current tt (advance current) prefix physical
      (published current (advance current) Database.committedAll)

  mutual
    pendingObservation : ∀ business saved remaining {events} final reply →
      E.Runs (runPending business saved remaining) events reply →
      X.Changes (active business saved remaining) events final →
      G.observe final reply ≡ normalizePending business saved remaining
    pendingObservation business saved [] final reply
      (E.replied _ _ tt (E.returned _))
      (X.changed _ _ _ _ (published _ _ Database.committedAll) (X.unchanged _)) = refl
    pendingObservation business saved (action ∷ rest) final reply execution physical with apply action business in applied
    ... | changed , answer with execution | physical
    ...   | E.replied _ _ tt runEvidence | X.changed _ _ _ _ (published _ _ Database.committedAll) remainingChanges rewrite applied =
            tailObservation changed (saved ++ ((action , answer) ∷ [])) rest final reply runEvidence remainingChanges

    tailObservation : ∀ business saved remaining {events} final reply →
      E.Runs (runTail business saved remaining) events reply →
      X.Changes (afterWrite business saved remaining) events final →
      G.observe final reply ≡ normalizePending business saved remaining
    tailObservation business saved [] .(finished business saved) .(finish saved)
      (E.returned _) (X.unchanged _) = refl
    tailObservation business saved remaining@(_ ∷ _) final reply execution physical =
      pendingObservation business saved remaining final reply execution physical

  stateObservation : ∀ current {events} final reply → E.Runs (runFromState current) events reply →
    X.Changes current events final → G.observe final reply ≡ normalize current
  stateObservation (finished business saved) .(finished business saved) .(finish saved)
    (E.returned _) (X.unchanged _) = refl
  stateObservation (active business saved remaining) final reply execution physical =
    pendingObservation business saved remaining final reply execution physical

  completedObservation : ∀ initial final reply → X.Completed (start tt) initial final reply →
    G.observe final reply ≡ normalize initial
  completedObservation initial final reply
    (X.completed _ (E.replied .inspect .runFromState .initial runEvidence)
      (X.changed .initial .inspect .initial .initial (inspected .initial) physical)) =
    stateObservation initial final reply runEvidence physical

  prependPublication : (current : State) (continuation : ⊤ → E.Script Wire.Value) (final : State) (reply : Wire.Value) →
    X.Completed (continuation tt) (advance current) final reply →
    X.Completed (E.ask (publish current) continuation) current final reply
  prependPublication current continuation final reply (X.completed events runEvidence physical) =
    X.completed ((publish current , tt) ∷ events)
      (E.replied (publish current) continuation tt runEvidence)
      (X.changed current (publish current) tt (advance current)
        (published current (advance current) Database.committedAll) physical)

  doneCompletes : (current : State) (reply : Wire.Value) → X.Completed (E.done reply) current current reply
  doneCompletes current reply = X.completed [] (E.returned reply) (X.unchanged current)

  prependKnownPublication : (current : State) (continuation : ⊤ → E.Script Wire.Value) (after final : State) (reply : Wire.Value) → after ≡ advance current →
    X.Completed (continuation tt) after final reply →
    X.Completed (E.ask (publish current) continuation) current final reply
  prependKnownPublication current continuation .(advance current) final reply refl completion =
    prependPublication current continuation final reply completion

  mutual
    pendingCompletes : ∀ business saved remaining →
      X.Completed (runPending business saved remaining) (active business saved remaining)
        (proj₁ (normalizePending business saved remaining)) (proj₂ (normalizePending business saved remaining))
    pendingCompletes business saved [] = prependPublication (active business saved []) _ _ _
      (doneCompletes (finished business saved) (finish saved))
    pendingCompletes business saved (action ∷ rest) with apply action business in applied
    ... | changed , answer = prependKnownPublication (active business saved (action ∷ rest)) _ _ _ _
      (sym (cong (λ pair → afterWrite (proj₁ pair) (saved ++ ((action , proj₂ pair) ∷ [])) rest) applied))
      (tailCompletes changed (saved ++ ((action , answer) ∷ [])) rest)

    tailCompletes : ∀ business saved remaining →
      X.Completed (runTail business saved remaining) (afterWrite business saved remaining)
        (proj₁ (normalizePending business saved remaining)) (proj₂ (normalizePending business saved remaining))
    tailCompletes business saved [] = doneCompletes (finished business saved) (finish saved)
    tailCompletes business saved remaining@(_ ∷ _) = pendingCompletes business saved remaining

  stateCompletes : ∀ current → X.Completed (runFromState current) current (proj₁ (normalize current)) (proj₂ (normalize current))
  stateCompletes (finished business saved) = doneCompletes (finished business saved) (finish saved)
  stateCompletes (active business saved remaining) = pendingCompletes business saved remaining

  progress : ∀ initial → Σ State (λ final → Σ Wire.Value (λ reply → X.Completed (start tt) initial final reply))
  progress initial with stateCompletes initial
  ... | X.completed events runEvidence physical = proj₁ (normalize initial) , proj₂ (normalize initial) ,
    X.completed ((inspect , initial) ∷ events)
      (E.replied inspect runFromState initial runEvidence)
      (X.changed initial inspect initial initial (inspected initial) physical)

  recoverable : (intent : G.Intent ⊤) →
    (∀ initial → normalize initial ≡ G.expected intent (G.invocation tt initial)) → Recoverable State ⊤
  recoverable intent correct = record
    { Effect = Effect
    ; Reply = Reply
    ; script = start
    ; Atomic = Atomic
    ; intent = intent
    ; converges = λ _ initial interrupted final reply interruption completion →
        trans (completedObservation interrupted final reply completion)
          (trans (interruptionsPreserveOutcome initial interrupted interruption) (correct initial))
    ; progress = λ _ initial → progress initial }
