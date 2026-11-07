{-# OPTIONS --safe #-}
-- The recovery goal is fixed here, outside operation implementations. Neither
-- an alternative predicate nor an operation-chosen observation is a field.
module Mimir.Recovery where

open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
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
