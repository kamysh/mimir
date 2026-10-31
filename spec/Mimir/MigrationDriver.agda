{-# OPTIONS --safe #-}
-- db.rs orchestration. Pure parser/validation functions and database replies
-- are explicit parameters, not axioms that they implement their contracts.
-- In particular a rollback queue receipt is NOT a PostgreSQL acknowledgement.
module Mimir.MigrationDriver where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
import Mimir.Effects as Effects
import Mimir.EffectRestriction as Restriction
import Mimir.MigrationFinalization as Finalization

module Driver (Problem Migration Receipt Checksums Snapshot : Set) where
  Result : Set → Set
  Result A = Problem ⊎ A

  record Pure : Set where
    field
      embedded : Result (List Migration)
      decodeReceipt : Result Receipt
      checkNames : List Migration → Result ⊤
      order : List Migration → Result (List Migration)
      checkChecksums : List Migration → Checksums → Result ⊤
      contains : Snapshot → Migration → Bool

  data Effect : Set where
    connect acquireLock ensureSchema : Effect
    loadChecksums loadAppliedForPublic : Effect
    beginTransaction setLocalSearchPath : Effect
    commitTransaction enqueueRollback releaseLock dropConnection : Effect
    importLegacy : Receipt → List Migration → Effect
    executeOriginalSQL recordBothLedgerRows : Migration → Effect

  Reply : Effect → Set
  Reply loadChecksums = Result Checksums
  Reply loadAppliedForPublic = Result Snapshot
  Reply enqueueRollback = ⊤
  Reply dropConnection = ⊤
  Reply _ = Result ⊤

  module E = Effects.Protocol Effect Reply
  open E public
  module F = Finalization.Finalize Problem

  close : Result ⊤ → Script (Result ⊤)
  close result = ask dropConnection (λ _ → done result)

  finalize : Result ⊤ → Script (Result ⊤)
  finalize result = ask releaseLock (λ unlocked → close (F.precedence result unlocked))

  -- Transaction::drop enqueues ROLLBACK synchronously on pre-commit failure.
  -- There is no await and thus no separate rollback error that can win here.
  abandon : Problem → Script (Result ⊤)
  abandon problem = ask enqueueRollback (λ _ → done (inj₁ problem))

  commit : Script (Result ⊤)
  commit = ask commitTransaction done

  recordLedger : Migration → Script (Result ⊤)
  recordLedger migration = ask (recordBothLedgerRows migration) λ where
    (inj₁ problem) → abandon problem
    (inj₂ tt) → commit

  execute : Migration → Script (Result ⊤)
  execute migration = ask (executeOriginalSQL migration) λ where
    (inj₁ problem) → abandon problem
    (inj₂ tt) → recordLedger migration

  setPath : Migration → Script (Result ⊤)
  setPath migration = ask setLocalSearchPath λ where
    (inj₁ problem) → abandon problem
    (inj₂ tt) → execute migration

  single : Migration → Script (Result ⊤)
  single migration = ask beginTransaction λ where
    (inj₁ problem) → done (inj₁ problem)
    (inj₂ tt) → setPath migration

  data TransactionEffect : Effect → Set where
    beginning : TransactionEffect beginTransaction
    path : TransactionEffect setLocalSearchPath
    sql : ∀ migration → TransactionEffect (executeOriginalSQL migration)
    ledger : ∀ migration → TransactionEffect (recordBothLedgerRows migration)
    committing : TransactionEffect commitTransaction
    rollingBack : TransactionEffect enqueueRollback

  module OnlyTransaction = Restriction.Restricted Effect Reply TransactionEffect

  abandonRestricted : ∀ problem → OnlyTransaction.Uses (abandon problem)
  abandonRestricted problem = OnlyTransaction.requested _ _ rollingBack
    (λ _ → OnlyTransaction.returned _)

  commitRestricted : OnlyTransaction.Uses commit
  commitRestricted = OnlyTransaction.requested _ _ committing
    (λ _ → OnlyTransaction.returned _)

  recordRestricted : ∀ migration → OnlyTransaction.Uses (recordLedger migration)
  recordRestricted migration = OnlyTransaction.requested _ _ (ledger migration) λ where
    (inj₁ problem) → abandonRestricted problem
    (inj₂ tt) → commitRestricted

  executeRestricted : ∀ migration → OnlyTransaction.Uses (execute migration)
  executeRestricted migration = OnlyTransaction.requested _ _ (sql migration) λ where
    (inj₁ problem) → abandonRestricted problem
    (inj₂ tt) → recordRestricted migration

  pathRestricted : ∀ migration → OnlyTransaction.Uses (setPath migration)
  pathRestricted migration = OnlyTransaction.requested _ _ path λ where
    (inj₁ problem) → abandonRestricted problem
    (inj₂ tt) → executeRestricted migration

  singleRestricted : ∀ migration → OnlyTransaction.Uses (single migration)
  singleRestricted migration = OnlyTransaction.requested _ _ beginning λ where
    (inj₁ problem) → OnlyTransaction.returned _
    (inj₂ tt) → pathRestricted migration

  module Run (pure : Pure) where
    open Pure pure

    each : Snapshot → List Migration → Script (Result ⊤)
    each snapshot [] = done (inj₂ tt)
    each snapshot (migration ∷ rest) with contains snapshot migration
    ... | true = each snapshot rest
    ... | false = single migration >>= λ where
      (inj₁ problem) → done (inj₁ problem)
      (inj₂ tt) → each snapshot rest

    -- The per-schema snapshot is an immutable argument to every recursive
    -- iteration. No path through the loop can reload either ledger, unlock,
    -- import history, or establish a fresh connection, even if interrupted.
    eachRestricted : ∀ snapshot migrations → OnlyTransaction.Uses (each snapshot migrations)
    eachRestricted snapshot [] = OnlyTransaction.returned _
    eachRestricted snapshot (migration ∷ rest) with contains snapshot migration
    ... | true = eachRestricted snapshot rest
    ... | false = OnlyTransaction.bindUses (singleRestricted migration) λ where
      (inj₁ problem) → OnlyTransaction.returned _
      (inj₂ tt) → eachRestricted snapshot rest

    checked : List Migration → Checksums → Snapshot → Script (Result ⊤)
    checked ordered checksums snapshot with checkChecksums ordered checksums
    ... | inj₁ problem = done (inj₁ problem)
    ... | inj₂ tt = each snapshot ordered

    readApplied : List Migration → Checksums → Script (Result ⊤)
    readApplied ordered checksums = ask loadAppliedForPublic λ where
      (inj₁ problem) → done (inj₁ problem)
      (inj₂ snapshot) → checked ordered checksums snapshot

    readChecksums : List Migration → Script (Result ⊤)
    readChecksums ordered = ask loadChecksums λ where
      (inj₁ problem) → done (inj₁ problem)
      (inj₂ checksums) → readApplied ordered checksums

    ensure : List Migration → Script (Result ⊤)
    ensure ordered = ask ensureSchema λ where
      (inj₁ problem) → done (inj₁ problem)
      (inj₂ tt) → readChecksums ordered

    sort : List Migration → Script (Result ⊤)
    sort migrations with order migrations
    ... | inj₁ problem = done (inj₁ problem)
    ... | inj₂ ordered = ensure ordered

    apply : List Migration → Script (Result ⊤)
    apply migrations with checkNames migrations
    ... | inj₁ problem = done (inj₁ problem)
    ... | inj₂ tt = sort migrations

    imported : Receipt → List Migration → Script (Result ⊤)
    imported receipt migrations = ask (importLegacy receipt migrations) λ where
      (inj₁ problem) → done (inj₁ problem)
      (inj₂ tt) → apply migrations

    decode : List Migration → Script (Result ⊤)
    decode migrations with decodeReceipt
    ... | inj₁ problem = close (inj₁ problem)
    ... | inj₂ receipt = imported receipt migrations >>= finalize

    lock : List Migration → Script (Result ⊤)
    lock migrations = ask acquireLock λ where
      (inj₁ problem) → close (inj₁ problem)
      (inj₂ tt) → decode migrations

    connecting : List Migration → Script (Result ⊤)
    connecting migrations = ask connect λ where
      (inj₁ problem) → done (inj₁ problem)
      (inj₂ tt) → lock migrations

    start : Script (Result ⊤)
    start with embedded
    ... | inj₁ problem = done (inj₁ problem)
    ... | inj₂ migrations = connecting migrations

    connectFailureOwnsNoConnection : ∀ migrations problem events result →
      Runs (connecting migrations) ((connect , inj₁ problem) ∷ events) result →
      events ≡ [] × result ≡ inj₁ problem
    connectFailureOwnsNoConnection _ _ _ _ (replied _ _ _ (returned _)) = refl , refl

    lockFailureDropsWithoutUnlock : ∀ migrations problem events result →
      Runs (lock migrations) ((acquireLock , inj₁ problem) ∷ events) result →
      events ≡ (dropConnection , tt) ∷ [] × result ≡ inj₁ problem
    lockFailureDropsWithoutUnlock _ _ _ _ (replied _ _ _ (replied _ _ tt (returned _))) = refl , refl

  finalizationTrace : ∀ primary unlocked events result →
    Runs (finalize primary) ((releaseLock , unlocked) ∷ events) result →
    events ≡ (dropConnection , tt) ∷ [] × result ≡ F.precedence primary unlocked
  finalizationTrace _ _ _ _ (replied _ _ _ (replied _ _ tt (returned _))) = refl , refl

  abandonTrace : ∀ problem events result → Runs (abandon problem) events result →
    events ≡ (enqueueRollback , tt) ∷ [] × result ≡ inj₁ problem
  abandonTrace _ _ _ (replied _ _ tt (returned _)) = refl , refl

  commitDoesNotRetryOrRollback : ∀ reply events result →
    Runs commit ((commitTransaction , reply) ∷ events) result →
    events ≡ [] × result ≡ reply
  commitDoesNotRetryOrRollback _ _ _ (replied _ _ _ (returned _)) = refl , refl

  beginFailureDoesNotDropUnownedTransaction : ∀ migration problem events result →
    Runs (single migration) ((beginTransaction , inj₁ problem) ∷ events) result →
    events ≡ [] × result ≡ inj₁ problem
  beginFailureDoesNotDropUnownedTransaction _ _ _ _ (replied _ _ _ (returned _)) = refl , refl

  successfulTrace : Migration → List Event
  successfulTrace migration =
    (beginTransaction , inj₂ tt) ∷ (setLocalSearchPath , inj₂ tt) ∷
    (executeOriginalSQL migration , inj₂ tt) ∷
    (recordBothLedgerRows migration , inj₂ tt) ∷
    (commitTransaction , inj₂ tt) ∷ []

  abandonNotSuccess : ∀ problem events → Runs (abandon problem) events (inj₂ tt) → ⊥
  abandonNotSuccess _ _ (replied _ _ tt ())

  commitSuccess : ∀ events → Runs commit events (inj₂ tt) →
    events ≡ (commitTransaction , inj₂ tt) ∷ []
  commitSuccess _ (replied _ _ (inj₁ _) ())
  commitSuccess _ (replied _ _ (inj₂ tt) (returned _)) = refl

  recordSuccess : ∀ migration events → Runs (recordLedger migration) events (inj₂ tt) →
    events ≡ (recordBothLedgerRows migration , inj₂ tt) ∷ (commitTransaction , inj₂ tt) ∷ []
  recordSuccess migration _ (replied _ _ (inj₁ problem) rest) =
    ⊥-elim (abandonNotSuccess problem _ rest)
  recordSuccess migration _ (replied _ _ (inj₂ tt) rest) =
    cong ((recordBothLedgerRows migration , inj₂ tt) ∷_) (commitSuccess _ rest)

  executeSuccess : ∀ migration events → Runs (execute migration) events (inj₂ tt) →
    events ≡ (executeOriginalSQL migration , inj₂ tt) ∷
      (recordBothLedgerRows migration , inj₂ tt) ∷ (commitTransaction , inj₂ tt) ∷ []
  executeSuccess migration _ (replied _ _ (inj₁ problem) rest) =
    ⊥-elim (abandonNotSuccess problem _ rest)
  executeSuccess migration _ (replied _ _ (inj₂ tt) rest) =
    cong ((executeOriginalSQL migration , inj₂ tt) ∷_) (recordSuccess migration _ rest)

  pathSuccess : ∀ migration events → Runs (setPath migration) events (inj₂ tt) →
    events ≡ (setLocalSearchPath , inj₂ tt) ∷ (executeOriginalSQL migration , inj₂ tt) ∷
      (recordBothLedgerRows migration , inj₂ tt) ∷ (commitTransaction , inj₂ tt) ∷ []
  pathSuccess migration _ (replied _ _ (inj₁ problem) rest) =
    ⊥-elim (abandonNotSuccess problem _ rest)
  pathSuccess migration _ (replied _ _ (inj₂ tt) rest) =
    cong ((setLocalSearchPath , inj₂ tt) ∷_) (executeSuccess migration _ rest)

  successRequiresAllReceipts : ∀ migration events →
    Runs (single migration) events (inj₂ tt) → events ≡ successfulTrace migration
  successRequiresAllReceipts migration _ (replied _ _ (inj₁ _) ())
  successRequiresAllReceipts migration _ (replied _ _ (inj₂ tt) rest) =
    cong ((beginTransaction , inj₂ tt) ∷_) (pathSuccess migration _ rest)
