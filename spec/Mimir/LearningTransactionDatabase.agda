{-# OPTIONS --safe #-}
-- Physical receipts for the existing executable learning transaction. Reads
-- use committed state at the acquired lock; only acknowledged complete writes
-- can reach commit. Native guarantees are parameters, not new postulates.
module Mimir.LearningTransactionDatabase where

open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
import Mimir.LearningTransaction as Transaction
import Mimir.DatabaseTransaction as Atomic
import Mimir.DatabaseReadCommitted as Committed
import Mimir.DatabaseAdvisoryLock as Lock

module Over (World Value Failure : Set) (database key : ℕ) where
  module T = Transaction.Over World Value Failure database key

  writeSet : World → T.Decision → World
  writeSet before (T.reject detail) = before
  writeSet before (T.replay value) = before
  writeSet before (T.replace proposed value) = proposed

  alternatives : ∀ (before proposed : World) receipt actual → Atomic.Atomic before proposed receipt actual →
    actual ≡ before ⊎ actual ≡ proposed
  alternatives before proposed receipt actual Atomic.committedAll = inj₂ refl
  alternatives before proposed receipt actual Atomic.abortedNone = inj₁ refl
  alternatives before proposed receipt actual Atomic.unknownBefore = inj₁ refl
  alternatives before proposed receipt actual Atomic.unknownAfter = inj₂ refl

  data NonPublication : T.Effect → Set where
    begin : ∀ db → NonPublication (T.begin db)
    acquire : ∀ tx lockKey → NonPublication (T.acquire tx lockKey)
    read : ∀ tx → NonPublication (T.read tx)
    write : ∀ tx proposed → NonPublication (T.write tx proposed)
    rollback : ∀ tx → NonPublication (T.rollback tx)

  -- Other operations may publish before this operation obtains its lock.
  -- Their actual scope transitions and atomic outcomes remain in the chain.
  data Publications : T.Scope → World → World → Set where
    unchanged : ∀ scope before → Publications scope before before
    advanced : ∀ {scope next effect reply before after} → T.Allowed scope (effect , reply) next →
      NonPublication effect → Publications next before after → Publications scope before after
    published : ∀ scope tx before proposed reply actual after →
      T.Allowed scope (T.commit tx , reply) T.finished → Atomic.Atomic before proposed (T.receipt reply) actual →
      Publications T.finished actual after → Publications scope before after

  finishedPeerCannotPublish : ∀ before after → Publications T.finished before after → after ≡ before
  finishedPeerCannotPublish before after (unchanged .T.finished .before) = refl
  finishedPeerCannotPublish before after (advanced () nonPublication rest)
  finishedPeerCannotPublish before after (published _ _ _ _ _ _ _ () atomic rest)

  module Bound (locks : Lock.Contract) (reads : Committed.Contract World)
    (nativeDatabase : Lock.Contract.Database locks) (nativeKey : Lock.Contract.Key locks)
    (nativeTransaction : ℕ → Lock.Contract.Transaction locks) (peerScope : T.Scope) where
    module L = Lock.Contract locks
    module C = Committed.Contract reads
    module Read = Committed.Application reads

    -- At the actual native operation point, this handle owns the requested
    -- database/key lock. ReviewCompetition ties acquisitions to one history.
    record HeldAt (tx : ℕ) : Set where
      field snapshot : L.Snapshot
            held : L.Held snapshot nativeDatabase nativeKey (nativeTransaction tx)

    data Session : Set where
      beginning : World → Session
      waiting reading ready : ℕ → World → Session
      written : ℕ → World → World → Session
      finished : World → Session

    view : Session → World
    view (beginning before) = before
    view (waiting tx before) = before
    view (reading tx before) = before
    view (ready tx before) = before
    view (written tx before proposed) = before
    view (finished actual) = actual

    record ReadAt (tx : ℕ) (before : World) : Set where
      field owned : HeldAt tx
            event : C.Read
            committed : C.committedAtStart event ≡ before
            untouched : C.ownPriorWrites event before ≡ before

    readSeesPublication : ∀ tx before (observed : ReadAt tx before) → C.snapshot (ReadAt.event observed) ≡ before
    readSeesPublication tx before observed = Read.readsPriorPublication (ReadAt.event observed) before
      (ReadAt.committed observed) (ReadAt.untouched observed)

    data Receipt : Session → T.E.Event → Session → Set where
      beginFailed : ∀ before error → Receipt (beginning before)
        (T.begin database , inj₁ error) (finished before)
      begun : ∀ before tx → Receipt (beginning before)
        (T.begin database , inj₂ tx) (waiting tx before)
      lockFailed : ∀ tx before error → Receipt (waiting tx before)
        (T.acquire tx key , inj₁ error) (waiting tx before)
      locked : ∀ tx before actual → Publications peerScope before actual → HeldAt tx →
        Receipt (waiting tx before) (T.acquire tx key , inj₂ tt) (reading tx actual)
      readFailed : ∀ tx before error → Receipt (reading tx before)
        (T.read tx , inj₁ error) (reading tx before)
      readSucceeded : ∀ tx before (observed : ReadAt tx before) → Receipt (reading tx before)
        (T.read tx , inj₂ (C.snapshot (ReadAt.event observed))) (ready tx before)
      writeFailed : ∀ tx before proposed error → Receipt (ready tx before)
        (T.write tx proposed , inj₁ error) (ready tx before)
      wrote : ∀ tx before proposed → HeldAt tx → Receipt (ready tx before)
        (T.write tx proposed , inj₂ tt) (written tx before proposed)
      committed : ∀ tx before proposed reply actual → HeldAt tx →
        Atomic.Atomic before proposed (T.receipt reply) actual → Receipt (written tx before proposed)
        (T.commit tx , reply) (finished actual)
      rollbackWaiting : ∀ tx before cleanup → Receipt (waiting tx before)
        (T.rollback tx , cleanup) (finished before)
      rollbackReading : ∀ tx before cleanup → Receipt (reading tx before)
        (T.rollback tx , cleanup) (finished before)
      rollbackReady : ∀ tx before cleanup → Receipt (ready tx before)
        (T.rollback tx , cleanup) (finished before)
      rollbackWritten : ∀ tx before proposed cleanup → Receipt (written tx before proposed)
        (T.rollback tx , cleanup) (finished before)

    data Runs : T.E.Script T.Outcome → Session → List T.E.Event → Session → T.Outcome → Set where
      returned : ∀ before result → Runs (T.E.done result) (finished before) [] (finished before) result
      replied : ∀ {before effect next reply middle events after result} → Receipt before (effect , reply) middle →
        Runs (next reply) middle events after result →
        Runs (T.E.ask effect next) before ((effect , reply) ∷ events) after result

    actualProgram : ∀ program before events after result → Runs program before events after result → T.E.Runs program events result
    actualProgram program before events after result (returned _ _) = T.E.returned _
    actualProgram program before events after result (replied receipt execution) = T.E.replied _ _ _ (actualProgram _ _ _ _ _ execution)

    data Inert : T.Decision → Set where
      reject : ∀ detail → Inert (T.reject detail)
      replay : ∀ value → Inert (T.replay value)

    decideCannotPublish : ∀ tx before decision events after result → Inert decision →
      Runs (T.decide tx decision) (ready tx before) events after result → after ≡ finished before
    decideCannotPublish tx before .(T.reject detail) events after result (reject detail)
      (replied (rollbackReady _ _ _) (returned _ _)) = refl
    decideCannotPublish tx before .(T.replay value) events after result (replay value)
      (replied (rollbackReady _ _ _) (returned _ _)) = refl

    afterLockCannotPublish : ∀ plan tx before events after result → Inert (plan before) →
      Runs (T.Plan.afterLock plan tx (inj₂ tt)) (reading tx before) events after result → after ≡ finished before
    afterLockCannotPublish plan tx before events after result inert
      (replied (readFailed _ _ _) (replied (rollbackReading _ _ _) (returned _ _))) = refl
    afterLockCannotPublish plan tx before events after result inert
      (replied (readSucceeded .tx .before observed) execution)
      rewrite readSeesPublication tx before observed = decideCannotPublish tx before (plan before) _ after result inert execution

    decisionPublication : ∀ tx before decision events after result →
      Runs (T.decide tx decision) (ready tx before) events after result →
      after ≡ finished before ⊎ after ≡ finished (writeSet before decision)
    decisionPublication tx before (T.reject detail) events after result execution =
      inj₁ (decideCannotPublish tx before (T.reject detail) events after result (reject detail) execution)
    decisionPublication tx before (T.replay value) events after result execution =
      inj₁ (decideCannotPublish tx before (T.replay value) events after result (replay value) execution)
    decisionPublication tx before (T.replace proposed value) events after result
      (replied (writeFailed _ _ _ _) (replied (rollbackReady _ _ _) (returned _ _))) = inj₁ refl
    decisionPublication tx before (T.replace proposed value) events after result
      (replied (wrote _ _ _ _) (replied (committed _ _ _ reply actual owned atomic) (returned _ _)))
      with alternatives before proposed (T.receipt reply) actual atomic
    ... | inj₁ sameBefore = inj₁ (cong finished sameBefore)
    ... | inj₂ saved = inj₂ (cong finished saved)

    readAndDecidePublication : ∀ plan tx before events after result →
      Runs (T.Plan.afterLock plan tx (inj₂ tt)) (reading tx before) events after result →
      after ≡ finished before ⊎ after ≡ finished (writeSet before (plan before))
    readAndDecidePublication plan tx before events after result
      (replied (readFailed _ _ _) (replied (rollbackReading _ _ _) (returned _ _))) = inj₁ refl
    readAndDecidePublication plan tx before events after result
      (replied (readSucceeded .tx .before observed) execution)
      rewrite readSeesPublication tx before observed = decisionPublication tx before (plan before) _ after result execution

  module AfterPeer (locks : Lock.Contract) (reads : Committed.Contract World)
    (nativeDatabase : Lock.Contract.Database locks) (nativeKey : Lock.Contract.Key locks)
    (nativeTransaction : ℕ → Lock.Contract.Transaction locks) where
    module B = Bound locks reads nativeDatabase nativeKey nativeTransaction T.finished

    acquisition : ∀ plan before events after result → B.Runs (T.Plan.start plan) (B.beginning before) events after result →
      Maybe (Σ ℕ B.HeldAt)
    acquisition plan before events after result (B.replied (B.beginFailed _ _) (B.returned _ _)) = nothing
    acquisition plan before events after result (B.replied (B.begun _ _) (B.replied (B.lockFailed _ _ _) execution)) = nothing
    acquisition plan before events after result (B.replied (B.begun _ tx) (B.replied (B.locked _ _ _ _ owned) execution)) = just (tx , owned)

    startCannotPublish : ∀ plan before events after result → B.Inert (plan before) →
      B.Runs (T.Plan.start plan) (B.beginning before) events after result → after ≡ B.finished before
    startCannotPublish plan before events after result inert
      (B.replied (B.beginFailed _ _) (B.returned _ _)) = refl
    startCannotPublish plan before events after result inert
      (B.replied (B.begun _ _) (B.replied (B.lockFailed _ _ _)
        (B.replied (B.rollbackWaiting _ _ _) (B.returned _ _)))) = refl
    startCannotPublish plan before events after result inert
      (B.replied (B.begun .before tx) (B.replied (B.locked .tx .before actual publications owned) execution))
      rewrite finishedPeerCannotPublish before actual publications = B.afterLockCannotPublish plan tx before _ after result inert execution

    startPublication : ∀ plan before events after result →
      B.Runs (T.Plan.start plan) (B.beginning before) events after result →
      after ≡ B.finished before ⊎ after ≡ B.finished (writeSet before (plan before))
    startPublication plan before events after result
      (B.replied (B.beginFailed _ _) (B.returned _ _)) = inj₁ refl
    startPublication plan before events after result
      (B.replied (B.begun _ _) (B.replied (B.lockFailed _ _ _)
        (B.replied (B.rollbackWaiting _ _ _) (B.returned _ _)))) = inj₁ refl
    startPublication plan before events after result
      (B.replied (B.begun .before tx) (B.replied (B.locked .tx .before actual publications owned) execution))
      rewrite finishedPeerCannotPublish before actual publications = B.readAndDecidePublication plan tx before _ after result execution
