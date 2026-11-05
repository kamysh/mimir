{-# OPTIONS --safe #-}
-- Exact outer error precedence and transaction-drop behavior in db.rs and
-- tokio-postgres 0.7.18. A queued rollback is not a database acknowledgement.
module Mimir.MigrationFinalization where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.Effects as Effects

data TransactionPhase : Set where openTransaction commitEntered finished : TransactionPhase

data LocalCleanup : Set where queueRollback noRollback : LocalCleanup

onDrop : TransactionPhase → LocalCleanup
onDrop openTransaction = queueRollback
onDrop commitEntered = noRollback
onDrop finished = noRollback

module Finalize (Problem : Set) where
  Result = Problem ⊎ ⊤

  -- The first result is from import/apply. Its error is returned even when
  -- the subsequently attempted unlock also fails.
  precedence : Result → Result → Result
  precedence (inj₁ primary) unlock = inj₁ primary
  precedence (inj₂ tt) unlock = unlock

  data Effect : Set where unlock dropConnection enqueueRollback : Effect

  Reply : Effect → Set
  Reply unlock = Result
  Reply dropConnection = ⊤
  Reply enqueueRollback = ⊤

  module E = Effects.Protocol Effect Reply
  open E public

  close : Result → Script Result
  close result = ask dropConnection (λ receipt → done result)

  afterApply : Result → Script Result
  afterApply result = ask unlock (λ reply → close (precedence result reply))

  receiptDecodeFailed : Problem → Script Result
  receiptDecodeFailed problem = close (inj₁ problem)

  dropTransaction : TransactionPhase → Script ⊤
  dropTransaction openTransaction = ask enqueueRollback (λ receipt → done tt)
  dropTransaction commitEntered = done tt
  dropTransaction finished = done tt

  originalErrorWins : ∀ primary secondary → precedence (inj₁ primary) secondary ≡ inj₁ primary
  originalErrorWins primary secondary = refl

  successfulApplyStillChecksUnlock : ∀ secondary → precedence (inj₂ tt) secondary ≡ secondary
  successfulApplyStillChecksUnlock secondary = refl

  commitDropDoesNotQueueRollback : ∀ events result →
    Runs (dropTransaction commitEntered) events result → events ≡ []
  commitDropDoesNotQueueRollback events result (returned _) = refl

  malformedReceiptOnlyDropsConnection : ∀ problem events result →
    Runs (receiptDecodeFailed problem) events result →
      events ≡ (dropConnection , tt) ∷ [] × result ≡ inj₁ problem
  malformedReceiptOnlyDropsConnection problem events result (replied _ _ tt (returned _)) = refl , refl

  failedApplyStillAttemptsUnlock : ∀ problem →
    afterApply (inj₁ problem) ≡ ask unlock (λ reply → close (inj₁ problem))
  failedApplyStillAttemptsUnlock problem = refl
