{-# OPTIONS --safe #-}
-- The recovery goal is fixed here, outside operation implementations. Neither
-- an alternative predicate nor an operation-chosen observation is a field.
module Mimir.Recovery where

open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; _++_; map; filterᵇ)
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
open import Data.Bool using (Bool; true; false; not)
open import Data.Integer using (ℤ)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.String using (toList)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; _≟_)
open import Mimir.Text using (Text)

-- Assembly fixes World once for the entire dispatcher. An operation over a
-- smaller world cannot be supplied where this dispatcher expects the larger
-- one. The observation retains the WHOLE world and the complete semantic reply.
module Outcome (World Result : Set) where
  Observation = World × Result

  observe : World → Result → Observation
  observe state reply = state , reply

  record Intent (Input : Set) : Set where
    field
      intended : Input → World → World
      expectedReply : Input → World → Result

  record Invocation (Input : Set) : Set where
    constructor invocation
    field
      input : Input
      initial : World

  expected : ∀ {Input} → Intent Input → Invocation Input → Observation
  expected intent call = observe
    (Intent.intended intent (Invocation.input call) (Invocation.initial call))
    (Intent.expectedReply intent (Invocation.input call) (Invocation.initial call))

  Goal : ∀ {Input} → Intent Input → Invocation Input → World → Result → Set
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

module Over (World : Set) = Outcome World Wire.Value

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

  changesAppend : ∀ {first middle last before after} →
    Changes first before middle → Changes middle after last →
    Changes first (before ++ after) last
  changesAppend (unchanged _) later = later
  changesAppend (changed before effect reply middle physical rest) later =
    changed before effect reply middle physical (changesAppend rest later)

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
    -- Preserve a semantic result before its public encoding. In particular,
    -- a read's missing-target or invalid-data result is not a JSON null.
    Result : Set
    Effect : Set
    Reply : Effect → Set
  module E = Effects.Protocol Effect Reply
  field
    script : Input → E.Script Result
    Atomic : World → (effect : Effect) → Reply effect → World → Set
    intent : Outcome.Intent World Result Input
  module X = Execution World Effect Reply Atomic
  module G = Outcome World Result
  field
    converges : ∀ input initial interrupted final reply →
      X.Interrupted (script input) initial interrupted →
      X.Completed (script input) interrupted final reply →
      G.Goal intent (G.invocation input initial) final reply
    progress : ∀ input initial →
      Σ World (λ final → Σ Result (λ reply →
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
    Σ World (λ final → Σ Result (λ reply →
      X.Completed (script input) initial final reply ×
      G.Goal intent (G.invocation input initial) final reply))
  progressReachesIntent input initial with progress input initial
  ... | final , reply , execution =
    final , reply , execution , completedMeetsIntent input initial final reply execution

-- Assembly selects the application meaning before it receives an operation.
-- The selected whole-world condition is a TYPE PARAMETER, never a field an
-- operation can replace. Numerical meaning can therefore require the complete
-- posterior equations without executing an arbitrarily capped solver here.
record RecoverableFor (World Input Result : Set)
  (Goal : Input → World → World → Result → Set) : Set₁ where
  field
    Effect : Set
    Reply : Effect → Set
  module E = Effects.Protocol Effect Reply
  field
    script : Input → E.Script Result
    Atomic : World → (effect : Effect) → Reply effect → World → Set
  module X = Execution World Effect Reply Atomic
  field
    converges : ∀ input initial interrupted final reply →
      X.Interrupted (script input) initial interrupted →
      X.Completed (script input) interrupted final reply →
      Goal input initial final reply
    progress : ∀ input initial →
      Σ World (λ final → Σ Result (λ reply →
        X.Completed (script input) initial final reply))

  completedMeetsGoal : ∀ input initial final reply →
    X.Completed (script input) initial final reply → Goal input initial final reply
  completedMeetsGoal input initial final reply execution =
    converges input initial initial final reply
      (X.atPrefix [] (script input) initial (E.stopped _) (X.unchanged initial)) execution

  progressReachesGoal : ∀ input initial →
    Σ World (λ final → Σ Result (λ reply →
      X.Completed (script input) initial final reply × Goal input initial final reply))
  progressReachesGoal input initial with progress input initial
  ... | final , reply , execution =
    final , reply , execution , completedMeetsGoal input initial final reply execution

-- Existing deterministic operations retain exactly their original complete
-- state-and-reply equality. This adapter does not reinterpret their scripts,
-- weaken their physical effects, or introduce another correctness premise.
module DeterministicContract {World Input : Set} (operation : Recoverable World Input) where
  module O = Recoverable operation
  module G = O.G

  Goal : Input → World → World → O.Result → Set
  Goal input initial final reply = G.Goal O.intent (G.invocation input initial) final reply

  operationFor : RecoverableFor World Input O.Result Goal
  operationFor = record
    { Effect = O.Effect
    ; Reply = O.Reply
    ; script = O.script
    ; Atomic = O.Atomic
    ; converges = O.converges
    ; progress = O.progress
    }

-- A dispatcher continuation must retain both its control prefix and the
-- physical meaning of every observed effect. No raw Script is a RunState.
module CheckedFor {World Input Result : Set} {Goal : Input → World → World → Result → Set}
  (operation : RecoverableFor World Input Result Goal) where
  module O = RecoverableFor operation
  module E = O.E
  module X = O.X

  record History (input : Input) (initial : World)
    (remaining : E.Script Result) : Set where
    constructor history
    field
      current : World
      events : List E.Event
      reached : E.Prefix (O.script input) events remaining
      physical : X.Changes initial events current

  record RunState (input : Input) (initial : World) : Set where
    constructor runState
    field
      remaining : E.Script Result
      evidence : History input initial remaining

  begin : ∀ input initial → RunState input initial
  begin input initial = runState (O.script input)
    (history initial [] (E.stopped _) (X.unchanged initial))

  advanceHistory : ∀ {input initial} effect continuation →
    (past : History input initial (E.ask effect continuation)) →
    (reply : O.Reply effect) → (after : World) →
    O.Atomic (History.current past) effect reply after →
    History input initial (continuation reply)
  advanceHistory effect continuation (history current events prefix physical) reply after meaning =
    history after (events ++ ((effect , reply) ∷ []))
      (E.prefixAppend prefix (E.replied effect continuation reply (E.stopped _)))
      (X.changesAppend physical
        (X.changed current effect reply after meaning (X.unchanged after)))

  -- The equality selects the request actually exposed by this continuation;
  -- the physical witness selects the world actually reached by its reply.
  advance : ∀ {input initial} (running : RunState input initial) effect continuation →
    RunState.remaining running ≡ E.ask effect continuation →
    (reply : O.Reply effect) → (after : World) →
    O.Atomic (History.current (RunState.evidence running)) effect reply after →
    RunState input initial
  advance (runState .(E.ask effect continuation) past) effect continuation refl reply after meaning =
    runState (continuation reply) (advanceHistory effect continuation past reply after meaning)

  prefixReturned : ∀ {script : E.Script Result} {events} {reply : Result} → E.Prefix script events (E.done reply) →
    E.Runs script events reply
  prefixReturned (E.stopped (E.done reply)) = E.returned reply
  prefixReturned (E.replied effect continuation reply rest) =
    E.replied effect continuation reply (prefixReturned rest)

  completed : ∀ {input initial reply} → (past : History input initial (E.done reply)) →
    X.Completed (O.script input) initial (History.current past) reply
  completed (history current events prefix physical) =
    X.completed events (prefixReturned prefix) physical

  finishedMeetsOriginalIntent : ∀ {input initial reply} →
    (past : History input initial (E.done reply)) →
    Goal input initial (History.current past) reply
  finishedMeetsOriginalIntent {input} {initial} {reply} past =
    O.completedMeetsGoal input initial (History.current past) reply (completed past)

  interrupt : ∀ {input initial remaining} → (past : History input initial remaining) →
    X.Interrupted (O.script input) initial (History.current past)
  interrupt (history current events prefix physical) =
    X.atPrefix events _ current prefix physical

  -- A committed change whose reply was lost is an interruption of the same
  -- original invocation. The unobserved reply is not appended to its history.
  loseReply : ∀ {input initial} effect continuation →
    (past : History input initial (E.ask effect continuation)) →
    (reply : O.Reply effect) → (after : World) →
    O.Atomic (History.current past) effect reply after →
    X.Interrupted (O.script input) initial after
  loseReply effect continuation (history current events prefix physical) reply after meaning =
    X.beforeReply events effect continuation current reply after prefix physical meaning

  retryAfterLostReplyMeetsOriginalIntent : ∀ {input initial} effect continuation →
    (past : History input initial (E.ask effect continuation)) →
    (unobserved : O.Reply effect) → (after final : World) → (reply : Result) →
    O.Atomic (History.current past) effect unobserved after →
    X.Completed (O.script input) after final reply →
    Goal input initial final reply
  retryAfterLostReplyMeetsOriginalIntent {input} {initial}
    effect continuation past unobserved after final reply meaning retry =
    O.converges input initial after final reply
      (loseReply effect continuation past unobserved after meaning) retry

module CheckedRun {World Input : Set} (operation : Recoverable World Input) =
  CheckedFor (DeterministicContract.operationFor operation)

-- One committed statement is not automatically repeatable. Its physical
-- meaning and independently reviewed intent are separate, and the complete
-- observation (including the reply) must be stable on replay.
module SingleResult (Result : Set) where
  record Statement (World Input : Set) : Set where
    field
      execute : Input → World → World × Result
      intent : Outcome.Intent World Result Input
      correct : ∀ input initial → execute input initial ≡
        Outcome.expected World Result intent (Outcome.invocation input initial)

  record Idempotent {World Input} (statement : Statement World Input) : Set where
    field
      stable : ∀ input initial →
        Statement.execute statement input (proj₁ (Statement.execute statement input initial)) ≡
        Statement.execute statement input initial

  module Semantics {World Input} (statement : Statement World Input) where
    execute = Statement.execute statement
    module G = Outcome World Result

    -- Only a confirmed statement supplies a completed reply. Aborts and lost
    -- acknowledgements remain interruption states, covered below directly
    -- from every constructor of the existing PostgreSQL atomicity contract.
    Atomic : World → Input → Result → World → Set
    Atomic before input reply after =
      Database.Atomic before (proj₁ (execute input before)) Database.committed after ×
      reply ≡ proj₂ (execute input before)

    module X = Execution World Input (λ _ → Result) Atomic
    module E = X.E

    script : Input → E.Script Result
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

    progress : ∀ input initial → Σ World (λ final → Σ Result (λ reply →
      X.Completed (script input) initial final reply))
    progress input initial = proj₁ (execute input initial) , proj₂ (execute input initial) ,
      X.completed ((input , proj₂ (execute input initial)) ∷ [])
        (E.replied input E.done (proj₂ (execute input initial)) (E.returned _))
        (X.changed initial input _ _ (Database.committedAll , refl) (X.unchanged _))

  single : ∀ {World Input} (statement : Statement World Input) →
    Idempotent statement → Recoverable World Input
  single {Input = Input} statement repeatable = record
    { Result = Result
    ; Effect = Input
    ; Reply = λ _ → Result
    ; script = S.script
    ; Atomic = S.Atomic
    ; intent = Statement.intent statement
    ; converges = S.converges repeatable
    ; progress = S.progress
    }
    where module S = Semantics statement

  readStatement : ∀ {World Input} → (Input → World → Result) → Statement World Input
  readStatement answer = record
    { execute = λ input initial → initial , answer input initial
    ; intent = record { intended = λ _ initial → initial; expectedReply = answer }
    ; correct = λ _ _ → refl
    }

  readIsIdempotent : ∀ {World Input} (answer : Input → World → Result) →
    Idempotent (readStatement answer)
  readIsIdempotent answer = record { stable = λ _ _ → refl }

  replyMustRepeat : ∀ {World Input} (statement : Statement World Input) →
    Idempotent statement → ∀ input initial →
    proj₂ (Statement.execute statement input (proj₁ (Statement.execute statement input initial))) ≡
    proj₂ (Statement.execute statement input initial)
  replyMustRepeat statement repeatable input initial =
    cong proj₂ (Idempotent.stable repeatable input initial)

module Single = SingleResult Wire.Value

-- A read owes its complete answer, not just a flag saying that it is read-only.
-- The application world is fixed here: graph, learning history, both vector
-- tables, documents and the operation journal all remain observable.
module ReadOnly {Input Result : Set} (answer : Input → Store.World → Result) where
  module S = SingleResult Result
  operation : Recoverable Store.World Input
  operation = S.single (S.readStatement answer) (S.readIsIdempotent answer)

  module Checked = Recoverable operation
  module Read = S.Semantics (S.readStatement answer)

  interruptedPreservesAllState : ∀ input initial interrupted →
    Checked.X.Interrupted (Checked.script input) initial interrupted → interrupted ≡ initial
  interruptedPreservesAllState input initial interrupted interruption
    with Read.interruptionState input initial interrupted interruption
  ... | inj₁ unchanged = unchanged
  ... | inj₂ unchanged = unchanged

  completedRetryPreservesStateAndAnswer : ∀ input initial interrupted final reply →
    Checked.X.Interrupted (Checked.script input) initial interrupted →
    Checked.X.Completed (Checked.script input) interrupted final reply →
    final ≡ initial × reply ≡ answer input initial
  completedRetryPreservesStateAndAnswer input initial interrupted final reply interruption completion =
    cong proj₁ outcome , cong proj₂ outcome
    where outcome = Checked.converges input initial interrupted final reply interruption completion

-- Reservation metadata is separate from business publication. Identities and
-- timestamps are supplied by PostgreSQL; this module has no identity generator
-- or uniqueness proposition. The database primary-key/default contracts apply.
module Reservations (Business Key Identity Timestamp : Set)
  (_≟_ : (first second : Key) → Dec (first ≡ second)) where

  record Entry : Set where
    constructor entry
    field token : Identity; reservedAt : Timestamp

  record State : Set where
    constructor state
    field business : Business; entries : List (Key × Entry)

  find : Key → List (Key × Entry) → Maybe Entry
  find key [] = nothing
  find key ((stored , allocated) ∷ rest) with key ≟ stored
  ... | yes _ = just allocated
  ... | no _ = find key rest

  readBack : State → Key → Maybe Entry
  readBack before key = find key (State.entries before)

  publish : State → Key → Entry → State
  publish before key allocated with readBack before key
  ... | just original = before
  ... | nothing = state (State.business before) ((key , allocated) ∷ State.entries before)

  reply : State → Key → Entry → Entry
  reply before key allocated with readBack before key
  ... | just original = original
  ... | nothing = allocated

  originalReservationIsReadable : ∀ before key allocated →
    readBack (publish before key allocated) key ≡ just (reply before key allocated)
  originalReservationIsReadable before key allocated with readBack before key in observed
  ... | just original = observed
  ... | nothing with key ≟ key
  ... | yes _ = refl
  ... | no impossible = ⊥-elim (impossible refl)

  existingReservationUnchanged : ∀ before key original allocated →
    readBack before key ≡ just original → publish before key allocated ≡ before
  existingReservationUnchanged before key original allocated observed rewrite observed = refl

  retryKeepsOriginalReservation : ∀ before key first second →
    publish (publish before key first) key second ≡ publish before key first
  retryKeepsOriginalReservation before key first second =
    existingReservationUnchanged (publish before key first) key (reply before key first) second
      (originalReservationIsReadable before key first)

  retryReturnsOriginalAnswer : ∀ before key first second →
    reply (publish before key first) key second ≡ reply before key first
  retryReturnsOriginalAnswer before key first second rewrite originalReservationIsReadable before key first = refl

  proposedPreservesBusiness : ∀ before key allocated →
    State.business (publish before key allocated) ≡ State.business before
  proposedPreservesBusiness before key allocated with readBack before key
  ... | just original = refl
  ... | nothing = refl

  businessUnchangedForEveryReceipt : ∀ before key allocated receipt after →
    Database.Atomic before (publish before key allocated) receipt after →
    State.business after ≡ State.business before
  businessUnchangedForEveryReceipt before key allocated receipt after publication =
    Database.invariantPreserved (λ current → State.business current ≡ State.business before)
      publication refl (proposedPreservesBusiness before key allocated)

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
-- The physical application journal is part of World. A business operation
-- cannot replace it with a private optional answer or discard unrelated rows.
module StoreFinalStep (Input : Set)
  (token : Input → ℕ) (key : Input → Text) (resultKey : Text)
  (distinct : ∀ input → ¬ (key input ≡ resultKey))
  (apply : Input → Store.World → Store.World × Wire.Value)
  (keepsJournal : ∀ input before →
    Store.World.operations (proj₁ (apply input before)) ≡ Store.World.operations before) where

  data Result : Set where
    done : Wire.Value → Result
    needsRecovery : Result
    cancelled : Store.CancellationRow → Result

  module G = Outcome Store.World Result
  module S = SingleResult Result

  firstPublication : Input → Store.World → Store.World
  firstPublication input before = Store.saveAnswer (proj₁ (apply input before))
    (token input) (key input) (proj₂ (apply input before))

  publication : Input → Store.World → Store.World
  publication input before = Store.saveAnswer (firstPublication input before)
    (token input) resultKey (proj₂ (apply input before))

  executeActive : Input → Store.World → Store.World × Result
  executeActive input before with Store.lookupSaved before (token input) (key input)
    | Store.lookupSaved before (token input) resultKey
  ... | just saved | just _ = before , done saved
  ... | nothing | nothing = publication input before , done (proj₂ (apply input before))
  ... | just _ | nothing = before , needsRecovery
  ... | nothing | just _ = before , needsRecovery

  replay : ∀ input before saved result →
    Store.lookupSaved before (token input) (key input) ≡ just saved →
    Store.lookupSaved before (token input) resultKey ≡ just result →
    executeActive input before ≡ (before , done saved)
  replay input before saved result observed completed rewrite observed | completed = refl

  missingResultPreservesWorld : ∀ input before saved →
    Store.lookupSaved before (token input) (key input) ≡ just saved →
    Store.lookupSaved before (token input) resultKey ≡ nothing →
    executeActive input before ≡ (before , needsRecovery)
  missingResultPreservesWorld input before saved observed missing rewrite observed | missing = refl

  missingStepPreservesWorld : ∀ input before result →
    Store.lookupSaved before (token input) (key input) ≡ nothing →
    Store.lookupSaved before (token input) resultKey ≡ just result →
    executeActive input before ≡ (before , needsRecovery)
  missingStepPreservesWorld input before result missing completed rewrite missing | completed = refl

  journalOfApplied : ∀ input before →
    Store.lookupSaved (proj₁ (apply input before)) (token input) (key input) ≡
    Store.lookupSaved before (token input) (key input)
  journalOfApplied input before = cong
    (λ tables → Store.lookupReply (token input) (key input) (Store.OperationTables.savedReplies tables))
    (keepsJournal input before)

  firstReadable : ∀ input before →
    Store.lookupSaved before (token input) (key input) ≡ nothing →
    Store.lookupSaved (Store.saveAnswer (proj₁ (apply input before))
      (token input) (key input) (proj₂ (apply input before))) (token input) (key input) ≡
      just (proj₂ (apply input before))
  firstReadable input before absent
    rewrite journalOfApplied input before | absent =
    Store.headReplyReadable (token input) (key input) (proj₂ (apply input before)) _

  publishedStepReadable : ∀ input before →
    Store.lookupSaved before (token input) (key input) ≡ nothing →
    Store.lookupSaved (publication input before) (token input) (key input) ≡ just (proj₂ (apply input before))
  publishedStepReadable input before absent = trans
    (Store.otherSavedAnswerPreserved (firstPublication input before) (token input) resultKey
      (proj₂ (apply input before)) (token input) (key input)
      (λ same → distinct input (proj₂ same)))
    (firstReadable input before absent)

  firstHasNoResult : ∀ input before →
    Store.lookupSaved before (token input) resultKey ≡ nothing →
    Store.lookupSaved (firstPublication input before) (token input) resultKey ≡ nothing
  firstHasNoResult input before absent = trans
    (Store.otherSavedAnswerPreserved (proj₁ (apply input before)) (token input) (key input)
      (proj₂ (apply input before)) (token input) resultKey
      (λ same → distinct input (sym (proj₂ same))))
    (trans (cong (λ tables → Store.lookupReply (token input) resultKey
      (Store.OperationTables.savedReplies tables)) (keepsJournal input before)) absent)

  publishedResultReadable : ∀ input before →
    Store.lookupSaved before (token input) resultKey ≡ nothing →
    Store.lookupSaved (publication input before) (token input) resultKey ≡ just (proj₂ (apply input before))
  publishedResultReadable input before absent
    rewrite firstHasNoResult input before absent =
    Store.headReplyReadable (token input) resultKey (proj₂ (apply input before)) _

  stableActive : ∀ input before → executeActive input (proj₁ (executeActive input before)) ≡ executeActive input before
  stableActive input before with Store.lookupSaved before (token input) (key input) in observed
    | Store.lookupSaved before (token input) resultKey in completed
  ... | just saved | just result = replay input before saved result observed completed
  ... | just saved | nothing rewrite observed | completed = refl
  ... | nothing | just result rewrite observed | completed = refl
  ... | nothing | nothing = replay input _ _ _ (publishedStepReadable input before observed)
    (Store.savedAnswerReadable (firstPublication input before) (token input) resultKey (proj₂ (apply input before)))

  publicationPreservesCancellation : ∀ input before →
    Store.lookupCancellation (publication input before) (token input) ≡ Store.lookupCancellation before (token input)
  publicationPreservesCancellation input before = trans
    (Store.savingAnswerPreservesCancellation (firstPublication input before) (token input) resultKey (proj₂ (apply input before)) (token input))
    (trans (Store.savingAnswerPreservesCancellation (proj₁ (apply input before)) (token input) (key input) (proj₂ (apply input before)) (token input))
      (cong (λ tables → Store.lookupCancellationRows (token input) (Store.OperationTables.cancellations tables)) (keepsJournal input before)))

  activePreservesCancellation : ∀ input before →
    Store.lookupCancellation (proj₁ (executeActive input before)) (token input) ≡ Store.lookupCancellation before (token input)
  activePreservesCancellation input before with Store.lookupSaved before (token input) (key input)
    | Store.lookupSaved before (token input) resultKey
  ... | just _ | just _ = refl
  ... | just _ | nothing = refl
  ... | nothing | just _ = refl
  ... | nothing | nothing = publicationPreservesCancellation input before

  execute : Input → Store.World → Store.World × Result
  execute input before with Store.lookupCancellation before (token input)
  ... | just original = before , cancelled original
  ... | nothing = executeActive input before

  cancellationBlocksEveryWrite : ∀ input before original →
    Store.lookupCancellation before (token input) ≡ just original →
    execute input before ≡ (before , cancelled original)
  cancellationBlocksEveryWrite input before original recorded rewrite recorded = refl

  stable : ∀ input before → execute input (proj₁ (execute input before)) ≡ execute input before
  stable input before with Store.lookupCancellation before (token input) in recorded
  ... | just original rewrite recorded = refl
  ... | nothing rewrite activePreservesCancellation input before | recorded = stableActive input before

  statement : (intent : G.Intent Input) →
    (∀ input initial → execute input initial ≡ G.expected intent (G.invocation input initial)) →
    S.Statement Store.World Input
  statement intent correct = record { execute = execute; intent = intent; correct = correct }

  recoverable : (intent : G.Intent Input) →
    (∀ input initial → execute input initial ≡ G.expected intent (G.invocation input initial)) →
    Recoverable Store.World Input
  recoverable intent correct = S.single (statement intent correct) (record { stable = stable })

-- Explicit cancellation is an application operation over the actual durable
-- rows. A saved result is returned unchanged; it is not inferred from business
-- data. PostgreSQL supplies the proposed cancellation timestamp externally.
module Cancellation where
  record Input : Set where
    constructor input
    field token : ℕ; cancelledAt : ℤ

  resultKey : Text
  resultKey = toList "@operation-result"

  reserved : ℕ → List Store.ReservationRow → Bool
  reserved token [] = false
  reserved token (row ∷ rest) with token ≟ Store.ReservationRow.token row
  ... | yes _ = true
  ... | no _ = reserved token rest

  owned : ℕ → Store.EmbeddingOwnerRow → Bool
  owned token owner with Store.EmbeddingOwnerRow.operationToken owner
  ... | nothing = false
  ... | just other with token ≟ other
  ... | yes _ = true
  ... | no _ = false

  retained : ℕ → List Store.EmbeddingOwnerRow → List Store.EmbeddingOwnerRow
  retained token = filterᵇ (λ owner → not (owned token owner))

  retainedStable : ∀ token owners → retained token (retained token owners) ≡ retained token owners
  retainedStable token [] = refl
  retainedStable token (owner ∷ rest) with owned token owner in ownership
  ... | true = retainedStable token rest
  ... | false rewrite ownership = cong (owner ∷_) (retainedStable token rest)

  retainedExcludes : ∀ token owners → All (λ owner → owned token owner ≡ false) (retained token owners)
  retainedExcludes token [] = []
  retainedExcludes token (owner ∷ rest) with owned token owner in ownership
  ... | true = retainedExcludes token rest
  ... | false = ownership ∷ retainedExcludes token rest

  otherOwnerSurvives : ∀ token owner owners → owned token owner ≡ false →
    Any (owner ≡_) owners → Any (owner ≡_) (retained token owners)
  otherOwnerSurvives token owner (.owner ∷ rest) keep (here refl) rewrite keep = here refl
  otherOwnerSurvives token owner (head ∷ rest) keep (there present) with owned token head
  ... | true = otherOwnerSurvives token owner rest keep present
  ... | false = there (otherOwnerSurvives token owner rest keep present)

  revoke : ℕ → Store.World → Store.World
  revoke token before = record before { embeddingOwners = retained token (Store.World.embeddingOwners before) }

  revokeStable : ∀ token before → revoke token (revoke token before) ≡ revoke token before
  revokeStable token before = cong (λ owners → record before { embeddingOwners = owners })
    (retainedStable token (Store.World.embeddingOwners before))

  publish : Input → Store.World → Store.World
  publish request before = record (revoke (Input.token request) before)
    { operations = record tables { cancellations =
        Store.cancellationRow (Input.token request) (Input.cancelledAt request) ∷
        Store.OperationTables.cancellations tables } }
    where tables = Store.World.operations before

  publicationKeepsRevocation : ∀ request before →
    revoke (Input.token request) (publish request before) ≡ publish request before
  publicationKeepsRevocation request before =
    cong (λ owners → record (publish request before) { embeddingOwners = owners })
      (retainedStable (Input.token request) (Store.World.embeddingOwners before))

  data Result : Set where
    unknownToken : Result
    savedResult : Wire.Value → Result
    cancelled : Store.CancellationRow → Result

  execute : Input → Store.World → Store.World × Result
  execute request before with reserved (Input.token request)
    (Store.OperationTables.reservations (Store.World.operations before))
  ... | false = before , unknownToken
  ... | true with Store.lookupSaved before (Input.token request) resultKey
  ... | just saved = before , savedResult saved
  ... | nothing with Store.lookupCancellation before (Input.token request)
  ... | just original = revoke (Input.token request) before , cancelled original
  ... | nothing = publish request before , cancelled
    (Store.cancellationRow (Input.token request) (Input.cancelledAt request))

  stable : ∀ request before → execute request (proj₁ (execute request before)) ≡ execute request before
  stable request before with reserved (Input.token request)
    (Store.OperationTables.reservations (Store.World.operations before)) in isReserved
  ... | false rewrite isReserved = refl
  ... | true with Store.lookupSaved before (Input.token request) resultKey in saved
  ... | just answer rewrite isReserved | saved = refl
  ... | nothing with Store.lookupCancellation before (Input.token request) in original
  ... | just old rewrite isReserved | saved | original |
      revokeStable (Input.token request) before = refl
  ... | nothing rewrite isReserved | saved |
      Store.headCancellationReadable (Input.token request) (Input.cancelledAt request)
        (Store.OperationTables.cancellations (Store.World.operations before)) |
      publicationKeepsRevocation request before = refl

  retryCannotChooseANewTime : ∀ token firstTime laterTime before →
    execute (input token laterTime) (proj₁ (execute (input token firstTime) before)) ≡
    execute (input token firstTime) before
  retryCannotChooseANewTime token firstTime laterTime before with reserved token
    (Store.OperationTables.reservations (Store.World.operations before)) in isReserved
  ... | false rewrite isReserved = refl
  ... | true with Store.lookupSaved before token resultKey in saved
  ... | just answer rewrite isReserved | saved = refl
  ... | nothing with Store.lookupCancellation before token in original
  ... | just old rewrite isReserved | saved | original | revokeStable token before = refl
  ... | nothing rewrite isReserved | saved |
      Store.headCancellationReadable token firstTime
        (Store.OperationTables.cancellations (Store.World.operations before)) |
      publicationKeepsRevocation (input token firstTime) before = refl

  intended : Input → Store.World → Store.World
  intended request before with reserved (Input.token request)
    (Store.OperationTables.reservations (Store.World.operations before))
  ... | false = before
  ... | true with Store.lookupSaved before (Input.token request) resultKey
  ... | just _ = before
  ... | nothing with Store.lookupCancellation before (Input.token request)
  ... | just _ = revoke (Input.token request) before
  ... | nothing = publish request before

  expectedReply : Input → Store.World → Result
  expectedReply request before with reserved (Input.token request)
    (Store.OperationTables.reservations (Store.World.operations before))
  ... | false = unknownToken
  ... | true with Store.lookupSaved before (Input.token request) resultKey
  ... | just saved = savedResult saved
  ... | nothing with Store.lookupCancellation before (Input.token request)
  ... | just original = cancelled original
  ... | nothing = cancelled (Store.cancellationRow (Input.token request) (Input.cancelledAt request))

  module S = SingleResult Result
  module G = Outcome Store.World Result

  intent : G.Intent Input
  intent = record { intended = intended; expectedReply = expectedReply }

  statement : S.Statement Store.World Input
  statement = record { execute = execute; intent = intent; correct = correct }
    where
    correct : ∀ request before → execute request before ≡ G.expected intent (G.invocation request before)
    correct request before with reserved (Input.token request)
      (Store.OperationTables.reservations (Store.World.operations before))
    ... | false = refl
    ... | true with Store.lookupSaved before (Input.token request) resultKey
    ... | just _ = refl
    ... | nothing with Store.lookupCancellation before (Input.token request)
    ... | just _ = refl
    ... | nothing = refl

  operation : Recoverable Store.World Input
  operation = S.single statement (record { stable = stable })

  Goal : Input → Store.World → Store.World → Result → Set
  Goal request initial final reply = (final , reply) ≡ (intended request initial , expectedReply request initial)

  module Checked = Recoverable operation
  certified : RecoverableFor Store.World Input Result Goal
  certified = record
    { Effect = Checked.Effect; Reply = Checked.Reply; script = Checked.script
    ; Atomic = Checked.Atomic; converges = Checked.converges; progress = Checked.progress }

  module Run = CheckedFor certified

  completedResultUnchanged : ∀ request before saved →
    reserved (Input.token request) (Store.OperationTables.reservations (Store.World.operations before)) ≡ true →
    Store.lookupSaved before (Input.token request) resultKey ≡ just saved →
    execute request before ≡ (before , savedResult saved)
  completedResultUnchanged request before saved isReserved observed rewrite isReserved | observed = refl

  businessUnchanged : ∀ request before → Store.businessSnapshot (proj₁ (execute request before)) ≡ Store.businessSnapshot before
  businessUnchanged request before with reserved (Input.token request)
    (Store.OperationTables.reservations (Store.World.operations before))
  ... | false = refl
  ... | true with Store.lookupSaved before (Input.token request) resultKey
  ... | just _ = refl
  ... | nothing with Store.lookupCancellation before (Input.token request)
  ... | just _ = refl
  ... | nothing = refl

  repliesUnchanged : ∀ request before →
    Store.OperationTables.savedReplies (Store.World.operations (proj₁ (execute request before))) ≡
    Store.OperationTables.savedReplies (Store.World.operations before)
  repliesUnchanged request before with reserved (Input.token request)
    (Store.OperationTables.reservations (Store.World.operations before))
  ... | false = refl
  ... | true with Store.lookupSaved before (Input.token request) resultKey
  ... | just _ = refl
  ... | nothing with Store.lookupCancellation before (Input.token request)
  ... | just _ = refl
  ... | nothing = refl

  originalInputsUnchanged : ∀ request before →
    let prior = Store.World.operations before
        after = Store.World.operations (proj₁ (execute request before))
    in (Store.OperationTables.reservations after , Store.OperationTables.requestKeys after ,
        Store.OperationTables.bindings after , Store.OperationTables.plans after) ≡
       (Store.OperationTables.reservations prior , Store.OperationTables.requestKeys prior ,
        Store.OperationTables.bindings prior , Store.OperationTables.plans prior)
  originalInputsUnchanged request before with reserved (Input.token request)
    (Store.OperationTables.reservations (Store.World.operations before))
  ... | false = refl
  ... | true with Store.lookupSaved before (Input.token request) resultKey
  ... | just _ = refl
  ... | nothing with Store.lookupCancellation before (Input.token request)
  ... | just _ = refl
  ... | nothing = refl

  previousCancellationsSurvive : ∀ request before old →
    Any (old ≡_) (Store.OperationTables.cancellations (Store.World.operations before)) →
    Any (old ≡_) (Store.OperationTables.cancellations (Store.World.operations (proj₁ (execute request before))))
  previousCancellationsSurvive request before old present with reserved (Input.token request)
    (Store.OperationTables.reservations (Store.World.operations before))
  ... | false = present
  ... | true with Store.lookupSaved before (Input.token request) resultKey
  ... | just _ = present
  ... | nothing with Store.lookupCancellation before (Input.token request)
  ... | just _ = present
  ... | nothing = there present

  everyReceiptPreservesBusiness : ∀ request before receipt actual →
    Database.Atomic before (proj₁ (execute request before)) receipt actual →
    Store.businessSnapshot actual ≡ Store.businessSnapshot before
  everyReceiptPreservesBusiness request before receipt actual publication =
    Database.invariantPreserved (λ world → Store.businessSnapshot world ≡ Store.businessSnapshot before)
      publication refl (businessUnchanged request before)

  cancelledIsReadable : ∀ request before after original →
    execute request before ≡ (after , cancelled original) →
    Store.lookupCancellation after (Input.token request) ≡ just original
  cancelledIsReadable request before after original observed with reserved (Input.token request)
    (Store.OperationTables.reservations (Store.World.operations before))
  cancelledIsReadable request before after original () | false
  ... | true with Store.lookupSaved before (Input.token request) resultKey
  cancelledIsReadable request before after original () | true | just _
  ... | nothing with Store.lookupCancellation before (Input.token request) in recorded
  cancelledIsReadable request before .(revoke (Input.token request) before) .old refl | true | nothing | just old = recorded
  cancelledIsReadable request before .(publish request before) .(Store.cancellationRow (Input.token request) (Input.cancelledAt request)) refl | true | nothing | nothing =
    Store.headCancellationReadable (Input.token request) (Input.cancelledAt request) _

  cancelledOwnersAbsent : ∀ request before after original →
    execute request before ≡ (after , cancelled original) →
    All (λ owner → owned (Input.token request) owner ≡ false) (Store.World.embeddingOwners after)
  cancelledOwnersAbsent request before after original observed with reserved (Input.token request)
    (Store.OperationTables.reservations (Store.World.operations before))
  cancelledOwnersAbsent request before after original () | false
  ... | true with Store.lookupSaved before (Input.token request) resultKey
  cancelledOwnersAbsent request before after original () | true | just _
  ... | nothing with Store.lookupCancellation before (Input.token request)
  cancelledOwnersAbsent request before .(revoke (Input.token request) before) .old refl | true | nothing | just old =
    retainedExcludes (Input.token request) (Store.World.embeddingOwners before)
  cancelledOwnersAbsent request before .(publish request before) .(Store.cancellationRow (Input.token request) (Input.cancelledAt request)) refl | true | nothing | nothing =
    retainedExcludes (Input.token request) (Store.World.embeddingOwners before)

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
    { Result = Wire.Value
    ; Effect = Effect
    ; Reply = Reply
    ; script = start
    ; Atomic = Atomic
    ; intent = intent
    ; converges = λ _ initial interrupted final reply interruption completion →
        trans (completedObservation interrupted final reply completion)
          (trans (interruptionsPreserveOutcome initial interrupted interruption) (correct initial))
    ; progress = λ _ initial → progress initial }
