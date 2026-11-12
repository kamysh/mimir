{-# OPTIONS --safe #-}
-- Mimir transaction orchestration, not PostgreSQL internals. Native adapters
-- must interpret every effect on the same handle and shared learning lock.
-- Partial write execution must stay uncommitted until the commit effect.
module Mimir.LearningTransaction where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Mimir.Text using (Text)
open import Mimir.UUIDGroups using (UUID)
import Mimir.Effects as Effects
import Mimir.DatabaseTransaction as Database
import Mimir.Recovery as Recovery

module Over (State Value Failure : Set) (database key : ℕ) where
  -- Identities name an adapter transaction, not a pool or client connection.
  Transaction = ℕ
  -- Both receipts confirm rollback and release of the owned transaction.
  -- Diagnostics are reported only after cleanup; the adapter must discard
  -- the connection if rollback cannot confirm release.
  data Cleanup : Set where
    cleaned : Cleanup
    cleanedWithDiagnostic : Failure → Cleanup

  data Decision : Set where
    reject : Failure → Decision
    replay : Value → Decision
    replace : State → Value → Decision

  data CommitReply : Set where
    committed : CommitReply
    aborted : Failure → CommitReply

  receipt : CommitReply → Database.Receipt
  receipt committed = Database.committed
  receipt (aborted detail) = Database.aborted

  data Phase : Set where
    beginning locking reading writing : Phase

  data Outcome : Set where
    failed : Phase → Failure → Maybe Cleanup → Outcome
    refused : Failure → Cleanup → Outcome
    replayed : Value → Cleanup → Outcome
    applied : Value → Outcome
    commitRejected : Value → Failure → Outcome

  data Effect : Set where
    begin : ℕ → Effect
    acquire : Transaction → ℕ → Effect
    read : Transaction → Effect
    write : Transaction → State → Effect
    allocateItem : Transaction → UUID → Text → Text → Text → Effect
    commit rollback : Transaction → Effect

  Reply : Effect → Set
  Reply (begin _) = Failure ⊎ Transaction
  Reply (acquire _ _) = Failure ⊎ ⊤
  Reply (read _) = Failure ⊎ State
  Reply (write _ _) = Failure ⊎ ⊤
  Reply (allocateItem _ _ _ _ _) = Failure ⊎ UUID
  Reply (commit _) = CommitReply
  Reply (rollback _) = Cleanup

  module E = Effects.Protocol Effect Reply

  committedOutcome : Value → CommitReply → Outcome
  committedOutcome value committed = applied value
  committedOutcome value (aborted detail) = commitRejected value detail

  close : Transaction → (Cleanup → Outcome) → E.Script Outcome
  close tx finish = E.ask (rollback tx) (λ cleanup → E.done (finish cleanup))

  afterWrite : Transaction → Value → Failure ⊎ ⊤ → E.Script Outcome
  afterWrite tx value (inj₁ detail) = close tx (λ cleanup → failed writing detail (just cleanup))
  afterWrite tx value (inj₂ tt) = E.ask (commit tx) (λ reply → E.done (committedOutcome value reply))

  decide : Transaction → Decision → E.Script Outcome
  decide tx (reject detail) = close tx (refused detail)
  decide tx (replay value) = close tx (replayed value)
  decide tx (replace proposed value) = E.ask (write tx proposed) (afterWrite tx value)

  module Plan (plan : State → Decision) where
    afterRead : Transaction → Failure ⊎ State → E.Script Outcome
    afterRead tx (inj₁ detail) = close tx (λ cleanup → failed reading detail (just cleanup))
    afterRead tx (inj₂ before) = decide tx (plan before)

    afterLock : Transaction → Failure ⊎ ⊤ → E.Script Outcome
    afterLock tx (inj₁ detail) = close tx (λ cleanup → failed locking detail (just cleanup))
    afterLock tx (inj₂ tt) = E.ask (read tx) (afterRead tx)

    afterBegin : Failure ⊎ Transaction → E.Script Outcome
    afterBegin (inj₁ detail) = E.done (failed beginning detail nothing)
    afterBegin (inj₂ tx) = E.ask (acquire tx key) (afterLock tx)

    start : E.Script Outcome
    start = E.ask (begin database) afterBegin

  -- Existing transaction plans share one recovery proof. The plan describes
  -- the requested state, independently of begin/lock/read/write orchestration.
  module RecoveryPlan (plan : State → Decision) where
    module Q = Plan plan

    publish : Decision → State → State
    publish (reject failure) before = before
    publish (replay value) before = before
    publish (replace proposed value) before = proposed

    intended : State → State
    intended before = publish (plan before) before

    Successful : Outcome → Set
    Successful (applied _) = ⊤
    Successful (replayed _ _) = ⊤
    Successful _ = ⊥

    Atomic : State → (effect : Effect) → Reply effect → State → Set
    Atomic before (read tx) (inj₂ observed) after = (after ≡ before) × (observed ≡ before)
    Atomic before (commit tx) reply after = Database.Atomic before (intended before) (receipt reply) after
    Atomic before _ _ after = after ≡ before

    module R = Recovery State Effect Outcome (λ _ → ⊤) Reply Atomic
      (λ before after → after ≡ before) (λ _ _ → State) (λ _ _ world → world)
      (λ _ world → world) Successful (λ _ → ⊤)

    closeInterrupted : ∀ tx finish before after → R.Interrupted (close tx finish) before after → after ≡ before
    closeInterrupted tx finish before after (R.stopped same) = same
    closeInterrupted tx finish before after (R.replied same ())

    writeInterrupted : ∀ tx value reply before after →
      R.Interrupted (afterWrite tx value reply) before after → after ≡ before
    writeInterrupted tx value (inj₁ error) before after attempt = closeInterrupted tx _ before after attempt
    writeInterrupted tx value (inj₂ tt) before after (R.stopped same) = same
    writeInterrupted tx value (inj₂ tt) before after (R.replied {reply = committed} atomic ())
    writeInterrupted tx value (inj₂ tt) before after (R.replied {reply = aborted error} atomic ())

    decisionInterrupted : ∀ tx decision before after →
      R.Interrupted (decide tx decision) before after → after ≡ before
    decisionInterrupted tx (reject error) before after attempt = closeInterrupted tx _ before after attempt
    decisionInterrupted tx (replay value) before after attempt = closeInterrupted tx _ before after attempt
    decisionInterrupted tx (replace proposed value) before after (R.stopped same) = same
    decisionInterrupted tx (replace proposed value) before after (R.replied {reply = reply} refl rest) =
      writeInterrupted tx value reply before after rest

    interruptedUnchanged : ∀ before after → R.Interrupted Q.start before after → after ≡ before
    interruptedUnchanged before after (R.stopped same) = same
    interruptedUnchanged before after (R.replied {reply = inj₁ error} refl ())
    interruptedUnchanged before after (R.replied {reply = inj₂ tx} refl (R.stopped same)) = same
    interruptedUnchanged before after (R.replied {reply = inj₂ tx} refl
      (R.replied {reply = inj₁ error} refl rest)) = closeInterrupted tx _ before after rest
    interruptedUnchanged before after (R.replied {reply = inj₂ tx} refl
      (R.replied {reply = inj₂ tt} refl (R.stopped same))) = same
    interruptedUnchanged before after (R.replied {reply = inj₂ tx} refl
      (R.replied {reply = inj₂ tt} refl (R.replied {reply = inj₁ error} refl rest))) =
      closeInterrupted tx _ before after rest
    interruptedUnchanged before after (R.replied {reply = inj₂ tx} refl
      (R.replied {reply = inj₂ tt} refl (R.replied {reply = inj₂ observed} (refl , refl) rest))) =
      decisionInterrupted tx (plan before) before after rest

    closeFailed : ∀ tx finish before after → R.Failed (close tx finish) before after → after ≡ before
    closeFailed tx finish before after (R.failedReply refl (R.failedReturn notSuccessful)) = refl

    writeFailed : ∀ tx value reply before after →
      R.Failed (afterWrite tx value reply) before after → after ≡ before
    writeFailed tx value (inj₁ error) before after attempt = closeFailed tx _ before after attempt
    writeFailed tx value (inj₂ tt) before after (R.failedReply {reply = committed} atomic (R.failedReturn notSuccessful)) =
      ⊥-elim (notSuccessful tt)
    writeFailed tx value (inj₂ tt) before after (R.failedReply {reply = aborted error} Database.abortedNone (R.failedReturn notSuccessful)) = refl

    decisionFailed : ∀ tx decision before after →
      R.Failed (decide tx decision) before after → after ≡ before
    decisionFailed tx (reject error) before after attempt = closeFailed tx _ before after attempt
    decisionFailed tx (replay value) before after attempt = closeFailed tx _ before after attempt
    decisionFailed tx (replace proposed value) before after (R.failedReply {reply = reply} refl rest) =
      writeFailed tx value reply before after rest

    failedUnchanged : ∀ before after → R.Failed Q.start before after → after ≡ before
    failedUnchanged before after (R.failedReply {reply = inj₁ error} refl (R.failedReturn notSuccessful)) = refl
    failedUnchanged before after (R.failedReply {reply = inj₂ tx} refl
      (R.failedReply {reply = inj₁ error} refl rest)) = closeFailed tx _ before after rest
    failedUnchanged before after (R.failedReply {reply = inj₂ tx} refl
      (R.failedReply {reply = inj₂ tt} refl (R.failedReply {reply = inj₁ error} refl rest))) =
      closeFailed tx _ before after rest
    failedUnchanged before after (R.failedReply {reply = inj₂ tx} refl
      (R.failedReply {reply = inj₂ tt} refl (R.failedReply {reply = inj₂ observed} (refl , refl) rest))) =
      decisionFailed tx (plan before) before after rest

    decisionCompletes : ∀ tx before after → R.Completed (decide tx (plan before)) before after → after ≡ intended before
    decisionCompletes tx before after complete with plan before in decision
    ... | reject error with complete
    ...   | R.replied atomic (R.returned ())
    decisionCompletes tx before after complete | replay value with complete
    ... | R.replied refl (R.returned succeeded) = refl
    decisionCompletes tx before after complete | replace proposed value with complete
    ... | R.replied {reply = inj₁ error} refl (R.replied atomic (R.returned ()))
    ... | R.replied {reply = inj₂ tt} refl (R.replied {reply = committed} Database.committedAll (R.returned succeeded)) =
      cong (λ chosen → publish chosen before) decision
    ... | R.replied {reply = inj₂ tt} refl (R.replied {reply = aborted error} atomic (R.returned ()))

    achieves : ∀ before after → R.Completed Q.start before after → after ≡ intended before
    achieves before after (R.replied {reply = inj₁ error} atomic (R.returned ()))
    achieves before after (R.replied {reply = inj₂ tx} refl
      (R.replied {reply = inj₁ error} atomic (R.replied cleanup (R.returned ()))))
    achieves before after (R.replied {reply = inj₂ tx} refl
      (R.replied {reply = inj₂ tt} refl (R.replied {reply = inj₁ error} atomic (R.replied cleanup (R.returned ())))))
    achieves before after (R.replied {reply = inj₂ tx} refl
      (R.replied {reply = inj₂ tt} refl (R.replied {reply = inj₂ observed} (refl , refl) rest))) =
      decisionCompletes tx before after rest

    atomicPlan : R.AllOrNothing ⊤
    atomicPlan = record
      { expected = λ _ before _ → intended before
      ; script = λ _ → Q.start
      ; interruptedUnchanged = λ _ → interruptedUnchanged
      ; failedUnchanged = λ _ → failedUnchanged
      ; achieves = λ _ before after completed _ → achieves before after completed
      }
    module Certified = R.Transactional atomicPlan
    recovery : R.Recoverable ⊤
    recovery = Certified.transactional

  -- Allocation is an observation on the already locked handle. It does not
  -- publish the pending owner/key rows independently of the enclosing write.
  data Allocation (A : Set) : Set where
    resolved : A → Allocation A
    reserve : UUID → Text → Text → Text → (Failure ⊎ UUID → Allocation A) → Allocation A

  bindAllocation : ∀ {A B} → Allocation A → (A → Allocation B) → Allocation B
  bindAllocation (resolved value) next = next value
  bindAllocation (reserve experience name source actor continuation) next =
    reserve experience name source actor (λ reply → bindAllocation (continuation reply) next)

  -- The result is selected by the observed database replies, not by a
  -- caller-chosen UUID or a deterministic interpretation of allocation.
  data Resolves {A : Set} : Allocation A → A → Set where
    resolvedResult : ∀ {value} → Resolves (resolved value) value
    reservedResult : ∀ {experience name source actor next value} reply →
      Resolves (next reply) value → Resolves (reserve experience name source actor next) value

  abstract
    resolvedValue : ∀ {A} {value result : A} → Resolves (resolved value) result → value ≡ result
    resolvedValue resolvedResult = refl

    bindResolution : ∀ {A B} (program : Allocation A) (next : A → Allocation B) result →
      Resolves (bindAllocation program next) result →
      Σ A (λ value → Resolves program value × Resolves (next value) result)
    bindResolution (resolved value) next result observed = value , resolvedResult , observed
    bindResolution (reserve experience name source actor continuation) next result (reservedResult reply observed)
      with bindResolution (continuation reply) next result observed
    ... | value , first , remaining = value , reservedResult reply first , remaining

  executeAllocation : Transaction → Allocation Decision → E.Script Outcome
  executeAllocation tx (resolved decision) = decide tx decision
  executeAllocation tx (reserve experience name source actor next) =
    E.ask (allocateItem tx experience name source actor) (λ reply → executeAllocation tx (next reply))

  module PreparedPlan (plan : State → Allocation Decision) where
    afterRead : Transaction → Failure ⊎ State → E.Script Outcome
    afterRead tx (inj₁ detail) = close tx (λ cleanup → failed reading detail (just cleanup))
    afterRead tx (inj₂ before) = executeAllocation tx (plan before)

    afterLock : Transaction → Failure ⊎ ⊤ → E.Script Outcome
    afterLock tx (inj₁ detail) = close tx (λ cleanup → failed locking detail (just cleanup))
    afterLock tx (inj₂ tt) = E.ask (read tx) (afterRead tx)

    afterBegin : Failure ⊎ Transaction → E.Script Outcome
    afterBegin (inj₁ detail) = E.done (failed beginning detail nothing)
    afterBegin (inj₂ tx) = E.ask (acquire tx key) (afterLock tx)

    start : E.Script Outcome
    start = E.ask (begin database) afterBegin

  -- Read and write require a successful lock receipt on this handle.
  -- Commit and cleanup receipts close and release the owned transaction.
  data Scope : Set where
    outside finished : Scope
    opened held : Transaction → Scope

  data Allowed : Scope → E.Event → Scope → Set where
    beginFailed : ∀ detail → Allowed outside (begin database , inj₁ detail) finished
    beginOpened : ∀ tx → Allowed outside (begin database , inj₂ tx) (opened tx)
    lockFailed : ∀ tx detail → Allowed (opened tx) (acquire tx key , inj₁ detail) (opened tx)
    lockHeld : ∀ tx → Allowed (opened tx) (acquire tx key , inj₂ tt) (held tx)
    readHeld : ∀ tx reply → Allowed (held tx) (read tx , reply) (held tx)
    writeHeld : ∀ tx proposed reply → Allowed (held tx) (write tx proposed , reply) (held tx)
    allocationHeld : ∀ tx experience name source actor reply →
      Allowed (held tx) (allocateItem tx experience name source actor , reply) (held tx)
    commitHeld : ∀ tx reply → Allowed (held tx) (commit tx , reply) finished
    rollbackOpened : ∀ tx reply → Allowed (opened tx) (rollback tx , reply) finished
    rollbackHeld : ∀ tx reply → Allowed (held tx) (rollback tx , reply) finished

  data Trace : Scope → List E.Event → Scope → Set where
    empty : ∀ scope → Trace scope [] scope
    more : ∀ {before next after event events} → Allowed before event next →
      Trace next events after → Trace before (event ∷ events) after

  data Scoped : Scope → E.Script Outcome → Set where
    done : ∀ outcome → Scoped finished (E.done outcome)
    ask : ∀ {scope effect next} →
      (∀ reply → Σ Scope (λ after → Allowed scope (effect , reply) after × Scoped after (next reply))) →
      Scoped scope (E.ask effect next)

  scopedRun : ∀ {scope program events result} → Scoped scope program → E.Runs program events result →
    Trace scope events finished
  scopedRun (done result) (E.returned .result) = empty finished
  scopedRun (ask next) (E.replied effect continuation reply execution) with next reply
  ... | after , allowed , scoped = more allowed (scopedRun scoped execution)

  scopedPrefix : ∀ {scope program events residual} → Scoped scope program → E.Prefix program events residual →
    Σ Scope (λ after → Trace scope events after × Scoped after residual)
  scopedPrefix {scope} proof (E.stopped program) = scope , empty scope , proof
  scopedPrefix (ask next) (E.replied effect continuation reply execution) with next reply
  ... | after , allowed , scoped with scopedPrefix scoped execution
  ... | final , trace , remaining = final , more allowed trace , remaining

  closeOpened : ∀ tx finish → Scoped (opened tx) (close tx finish)
  closeOpened tx finish = ask
    (λ reply →
       finished , rollbackOpened tx reply , done (finish reply))

  closeHeld : ∀ tx finish → Scoped (held tx) (close tx finish)
  closeHeld tx finish = ask
    (λ reply → finished , rollbackHeld tx reply , done (finish reply))

  writeScoped : ∀ tx value reply → Scoped (held tx) (afterWrite tx value reply)
  writeScoped tx value (inj₁ detail) = closeHeld tx (λ cleanup → failed writing detail (just cleanup))
  writeScoped tx value (inj₂ tt) = ask
    (λ reply →
       finished ,
       commitHeld tx reply , done (committedOutcome value reply))

  decideScoped : ∀ tx decision → Scoped (held tx) (decide tx decision)
  decideScoped tx (reject detail) = closeHeld tx (refused detail)
  decideScoped tx (replay value) = closeHeld tx (replayed value)
  decideScoped tx (replace proposed value) = ask
    (λ reply →
       held tx , writeHeld tx proposed reply , writeScoped tx value reply)

  allocationScoped : ∀ tx plan → Scoped (held tx) (executeAllocation tx plan)
  allocationScoped tx (resolved decision) = decideScoped tx decision
  allocationScoped tx (reserve experience name source actor next) = ask
    (λ reply → held tx , allocationHeld tx experience name source actor reply , allocationScoped tx (next reply))

  module PreparedLaws (plan : State → Allocation Decision) where
    open PreparedPlan plan

    readScoped : ∀ tx reply → Scoped (held tx) (afterRead tx reply)
    readScoped tx (inj₁ detail) = closeHeld tx (λ cleanup → failed reading detail (just cleanup))
    readScoped tx (inj₂ before) = allocationScoped tx (plan before)

    lockScoped : ∀ tx reply → Σ Scope (λ after →
      Allowed (opened tx) (acquire tx key , reply) after × Scoped after (afterLock tx reply))
    lockScoped tx (inj₁ detail) = opened tx , lockFailed tx detail ,
      closeOpened tx (λ cleanup → failed locking detail (just cleanup))
    lockScoped tx (inj₂ tt) = held tx , lockHeld tx , ask
      (λ response → held tx , readHeld tx response , readScoped tx response)

    startScoped : Scoped outside start
    startScoped = ask λ where
      (inj₁ detail) → finished , beginFailed detail , done (failed beginning detail nothing)
      (inj₂ tx) → opened tx , beginOpened tx , ask (λ response → lockScoped tx response)

    completedScope : ∀ events result → E.Runs start events result → Trace outside events finished
    completedScope events result = scopedRun startScoped

    interruptedScope : ∀ events residual → E.Prefix start events residual →
      Σ Scope (λ after → Trace outside events after × Scoped after residual)
    interruptedScope events residual = scopedPrefix startScoped

  module Laws (plan : State → Decision) where
    open Plan plan

    readScoped : ∀ tx reply → Scoped (held tx) (afterRead tx reply)
    readScoped tx (inj₁ detail) = closeHeld tx (λ cleanup → failed reading detail (just cleanup))
    readScoped tx (inj₂ before) = decideScoped tx (plan before)

    lockScoped : ∀ tx reply → Σ Scope (λ after →
      Allowed (opened tx) (acquire tx key , reply) after × Scoped after (afterLock tx reply))
    lockScoped tx (inj₁ detail) = opened tx , lockFailed tx detail ,
      closeOpened tx (λ cleanup → failed locking detail (just cleanup))
    lockScoped tx (inj₂ tt) = held tx ,
      lockHeld tx ,
      ask
      (λ response →
         held tx , readHeld tx response , readScoped tx response)

    startScoped : Scoped outside start
    startScoped = ask
      (λ { (inj₁ detail)
             → finished , beginFailed detail , done
               (failed beginning detail nothing)
         ; (inj₂ tx) → opened tx , beginOpened tx , ask (λ response → lockScoped tx response)
         })

    completedScope : ∀ events result → E.Runs start events result → Trace outside events finished
    completedScope events result = scopedRun startScoped

    interruptedScope : ∀ events residual → E.Prefix start events residual →
      Σ Scope (λ after → Trace outside events after × Scoped after residual)
    interruptedScope events residual = scopedPrefix startScoped

  readNeedsHeld : ∀ {before tx reply after} → Allowed before (read tx , reply) after → before ≡ held tx
  readNeedsHeld (readHeld tx reply) = refl

  writeNeedsHeld : ∀ {before tx proposed reply after} →
    Allowed before (write tx proposed , reply) after → before ≡ held tx
  writeNeedsHeld (writeHeld tx proposed reply) = refl

  commitNeedsHeld : ∀ {before tx reply after} → Allowed before (commit tx , reply) after → before ≡ held tx
  commitNeedsHeld (commitHeld tx reply) = refl

  allocationNeedsHeld : ∀ {before tx experience name source actor reply after} →
    Allowed before (allocateItem tx experience name source actor , reply) after → before ≡ held tx
  allocationNeedsHeld (allocationHeld tx experience name source actor reply) = refl

  -- Private preparation ends either with confirmed cleanup or with the one
  -- transaction that is ready to commit. It cannot publish business changes.
  module Staging (plan : State → Allocation Decision) where
    NoCommit : Effect → Set
    NoCommit (commit tx) = ⊥
    NoCommit (begin database) = ⊤
    NoCommit (acquire tx key) = ⊤
    NoCommit (read tx) = ⊤
    NoCommit (write tx proposed) = ⊤
    NoCommit (allocateItem tx experience name source actor) = ⊤
    NoCommit (rollback tx) = ⊤

    PreparationEffect = Σ Effect NoCommit
    PreparationReply : PreparationEffect → Set
    PreparationReply (effect , witness) = Reply effect
    module P = Effects.Protocol PreparationEffect PreparationReply

    Uncommitted : Outcome → Set
    Uncommitted (applied value) = ⊥
    Uncommitted (failed phase detail cleanup) = ⊤
    Uncommitted (refused detail cleanup) = ⊤
    Uncommitted (replayed value cleanup) = ⊤
    Uncommitted (commitRejected value detail) = ⊤

    data Result : Set where
      complete : (outcome : Outcome) → Uncommitted outcome → Result
      ready : Transaction → State → Value → Result

    closeStage : ∀ tx (finish : Cleanup → Outcome) →
      (∀ cleanup → Uncommitted (finish cleanup)) → P.Script Result
    closeStage tx finish proof = P.ask (rollback tx , tt)
      (λ cleanup → P.done (complete (finish cleanup) (proof cleanup)))

    afterStageWrite : Transaction → State → Value → Failure ⊎ ⊤ → P.Script Result
    afterStageWrite tx proposed value (inj₁ detail) = closeStage tx
      (λ cleanup → failed writing detail (just cleanup)) (λ _ → tt)
    afterStageWrite tx proposed value (inj₂ tt) = P.done (ready tx proposed value)

    stageDecision : Transaction → Decision → P.Script Result
    stageDecision tx (reject detail) = closeStage tx (refused detail) (λ _ → tt)
    stageDecision tx (replay value) = closeStage tx (replayed value) (λ _ → tt)
    stageDecision tx (replace proposed value) = P.ask (write tx proposed , tt) (afterStageWrite tx proposed value)

    stageAllocation : Transaction → Allocation Decision → P.Script Result
    stageAllocation tx (resolved decision) = stageDecision tx decision
    stageAllocation tx (reserve experience name source actor next) =
      P.ask (allocateItem tx experience name source actor , tt) (λ reply → stageAllocation tx (next reply))

    afterStageRead : Transaction → Failure ⊎ State → P.Script Result
    afterStageRead tx (inj₁ detail) = closeStage tx
      (λ cleanup → failed reading detail (just cleanup)) (λ _ → tt)
    afterStageRead tx (inj₂ before) = stageAllocation tx (plan before)

    afterStageLock : Transaction → Failure ⊎ ⊤ → P.Script Result
    afterStageLock tx (inj₁ detail) = closeStage tx
      (λ cleanup → failed locking detail (just cleanup)) (λ _ → tt)
    afterStageLock tx (inj₂ tt) = P.ask (read tx , tt) (afterStageRead tx)

    afterStageBegin : Failure ⊎ Transaction → P.Script Result
    afterStageBegin (inj₁ detail) = P.done (complete (failed beginning detail nothing) tt)
    afterStageBegin (inj₂ tx) = P.ask (acquire tx key , tt) (afterStageLock tx)

    start : P.Script Result
    start = P.ask (begin database , tt) afterStageBegin

    -- In particular, an error cannot be returned while its transaction is
    -- still held. A ready transaction must instead reach commit or cleanup.
    data StagedScope : Scope → P.Script Result → Set where
      closed : ∀ outcome proof → StagedScope finished (P.done (complete outcome proof))
      prepared : ∀ tx proposed value → StagedScope (held tx) (P.done (ready tx proposed value))
      step : ∀ {scope effect witness next} →
        (∀ reply → Σ Scope (λ after → Allowed scope (effect , reply) after × StagedScope after (next reply))) →
        StagedScope scope (P.ask (effect , witness) next)

    closeOpenedStage : ∀ tx finish proof → StagedScope (opened tx) (closeStage tx finish proof)
    closeOpenedStage tx finish proof = step (λ reply → finished , rollbackOpened tx reply , closed _ _)

    closeHeldStage : ∀ tx finish proof → StagedScope (held tx) (closeStage tx finish proof)
    closeHeldStage tx finish proof = step (λ reply → finished , rollbackHeld tx reply , closed _ _)

    writeStageScoped : ∀ tx proposed value reply → StagedScope (held tx) (afterStageWrite tx proposed value reply)
    writeStageScoped tx proposed value (inj₁ detail) = closeHeldStage tx _ _
    writeStageScoped tx proposed value (inj₂ tt) = prepared tx proposed value

    decisionStageScoped : ∀ tx decision → StagedScope (held tx) (stageDecision tx decision)
    decisionStageScoped tx (reject detail) = closeHeldStage tx _ _
    decisionStageScoped tx (replay value) = closeHeldStage tx _ _
    decisionStageScoped tx (replace proposed value) = step
      (λ reply → held tx , writeHeld tx proposed reply , writeStageScoped tx proposed value reply)

    allocationStageScoped : ∀ tx allocation → StagedScope (held tx) (stageAllocation tx allocation)
    allocationStageScoped tx (resolved decision) = decisionStageScoped tx decision
    allocationStageScoped tx (reserve experience name source actor next) = step
      (λ reply → held tx , allocationHeld tx experience name source actor reply , allocationStageScoped tx (next reply))

    readStageScoped : ∀ tx reply → StagedScope (held tx) (afterStageRead tx reply)
    readStageScoped tx (inj₁ detail) = closeHeldStage tx _ _
    readStageScoped tx (inj₂ before) = allocationStageScoped tx (plan before)

    lockStageScoped : ∀ tx reply → Σ Scope (λ after →
      Allowed (opened tx) (acquire tx key , reply) after × StagedScope after (afterStageLock tx reply))
    lockStageScoped tx (inj₁ detail) = opened tx , lockFailed tx detail , closeOpenedStage tx _ _
    lockStageScoped tx (inj₂ tt) = held tx , lockHeld tx , step
      (λ response → held tx , readHeld tx response , readStageScoped tx response)

    startScoped : StagedScope outside start
    startScoped = step λ where
      (inj₁ detail) → finished , beginFailed detail , closed _ _
      (inj₂ tx) → opened tx , beginOpened tx , step (λ reply → lockStageScoped tx reply)

    completedPreparationIsClosed : ∀ {scope outcome proof} →
      StagedScope scope (P.done (complete outcome proof)) → scope ≡ finished
    completedPreparationIsClosed (closed outcome proof) = refl

    readyPreparationOwnsTransaction : ∀ {scope tx proposed value} →
      StagedScope scope (P.done (ready tx proposed value)) → scope ≡ held tx
    readyPreparationOwnsTransaction (prepared tx proposed value) = refl

  finishedNoEffects : ∀ {events after} → Trace finished events after → events ≡ []
  finishedNoEffects (empty .finished) = refl
  finishedNoEffects (more () rest)

  closeOnlyRollback : ∀ tx finish events result → E.Runs (close tx finish) events result →
    Σ Cleanup (λ cleanup → events ≡ ((rollback tx , cleanup) ∷ []) × result ≡ finish cleanup)
  closeOnlyRollback tx finish events result (E.replied _ _ cleanup (E.returned _)) = cleanup , refl , refl

  exactReplayOnlyRollback : ∀ tx value events result → E.Runs (decide tx (replay value)) events result →
    Σ Cleanup (λ cleanup → events ≡ ((rollback tx , cleanup) ∷ []) × result ≡ replayed value cleanup)
  exactReplayOnlyRollback tx value = closeOnlyRollback tx (replayed value)

  rejectionOnlyRollback : ∀ tx detail events result → E.Runs (decide tx (reject detail)) events result →
    Σ Cleanup (λ cleanup → events ≡ ((rollback tx , cleanup) ∷ []) × result ≡ refused detail cleanup)
  rejectionOnlyRollback tx detail = closeOnlyRollback tx (refused detail)
