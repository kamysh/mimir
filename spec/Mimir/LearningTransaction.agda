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
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.Effects as Effects
import Mimir.DatabaseTransaction as Database

module Over (State Value Failure : Set) (database key : ℕ) where
  -- Identities name an adapter transaction, not a pool or client connection.
  Transaction = ℕ
  Cleanup = Failure ⊎ ⊤

  data Decision : Set where
    reject : Failure → Decision
    replay : Value → Decision
    replace : State → Value → Decision

  data CommitReply : Set where
    committed : CommitReply
    aborted unknown : Failure → CommitReply

  receipt : CommitReply → Database.Receipt
  receipt committed = Database.committed
  receipt (aborted detail) = Database.aborted
  receipt (unknown detail) = Database.acknowledgementLost

  data Phase : Set where
    beginning locking reading writing : Phase

  data Outcome : Set where
    failed : Phase → Failure → Maybe Cleanup → Outcome
    refused : Failure → Cleanup → Outcome
    replayed : Value → Cleanup → Outcome
    applied : Value → Outcome
    commitRejected commitUncertain : Value → Failure → Outcome

  data Effect : Set where
    begin : ℕ → Effect
    acquire : Transaction → ℕ → Effect
    read : Transaction → Effect
    write : Transaction → State → Effect
    allocateItem : Transaction → ℕ → Text → Text → Text → Effect
    commit rollback : Transaction → Effect

  Reply : Effect → Set
  Reply (begin _) = Failure ⊎ Transaction
  Reply (acquire _ _) = Failure ⊎ ⊤
  Reply (read _) = Failure ⊎ State
  Reply (write _ _) = Failure ⊎ ⊤
  Reply (allocateItem _ _ _ _ _) = Failure ⊎ ℕ
  Reply (commit _) = CommitReply
  Reply (rollback _) = Cleanup

  module E = Effects.Protocol Effect Reply

  committedOutcome : Value → CommitReply → Outcome
  committedOutcome value committed = applied value
  committedOutcome value (aborted detail) = commitRejected value detail
  committedOutcome value (unknown detail) = commitUncertain value detail

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

  -- Allocation is an observation on the already locked handle. It does not
  -- publish the pending owner/key rows independently of the enclosing write.
  data Allocation (A : Set) : Set where
    resolved : A → Allocation A
    reserve : ℕ → Text → Text → Text → (Failure ⊎ ℕ → Allocation A) → Allocation A

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

  -- An independent effect policy. Read and write require a successful lock
  -- receipt on this handle. Closing ends the application trace even if the
  -- rollback acknowledgement failed; it does not assert database release.
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
