{-# OPTIONS --safe #-}
-- kryzhen 2.0.3 record_applied uses GenericClient::transaction. On a Client
-- this is BEGIN/COMMIT; on Mimir's outer Transaction it is SAVEPOINT/RELEASE.
-- A successful nested release does not publish the outer SQL transaction.
module Mimir.MigrationLedgerWrite where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
import Mimir.Effects as Effects
import Mimir.EffectRestriction as Restriction

data Context : Set where standalone nested : Context

data Command : Set where
  begin savepoint commit releaseSavepoint rollback rollbackToSavepoint : Command

enter : Context → Command
enter standalone = begin
enter nested = savepoint

finish : Context → Command
finish standalone = commit
finish nested = releaseSavepoint

abort : Context → Command
abort standalone = rollback
abort nested = rollbackToSavepoint

module Write (Problem Migration Schema : Set) where
  Result = Problem ⊎ ⊤

  data Effect : Set where
    awaitCommand : Command → Effect
    enqueue : Command → Effect
    insertCanonical : Migration → Effect
    insertAssociation : Migration → Schema → Effect

  Reply : Effect → Set
  Reply (enqueue _) = ⊤
  Reply _ = Result

  module E = Effects.Protocol Effect Reply
  open E public

  abandon : Context → Problem → Script Result
  abandon context problem = ask (enqueue (abort context)) (λ _ → done (inj₁ problem))

  publish : Context → Script Result
  publish context = ask (awaitCommand (finish context)) done

  association : Context → Migration → Schema → Script Result
  association context migration schema = ask (insertAssociation migration schema) λ where
    (inj₁ problem) → abandon context problem
    (inj₂ tt) → publish context

  canonical : Context → Migration → Schema → Script Result
  canonical context migration schema = ask (insertCanonical migration) λ where
    (inj₁ problem) → abandon context problem
    (inj₂ tt) → association context migration schema

  recordApplied : Context → Migration → Schema → Script Result
  recordApplied context migration schema = ask (awaitCommand (enter context)) λ where
    (inj₁ problem) → done (inj₁ problem)
    (inj₂ tt) → canonical context migration schema

  -- A finite trace or interrupted prefix of nested recording cannot contain
  -- an outer COMMIT or outer ROLLBACK. The caller still owns that transaction.
  data NestedEffect : Effect → Set where
    entering : NestedEffect (awaitCommand savepoint)
    leaving : NestedEffect (awaitCommand releaseSavepoint)
    queued : NestedEffect (enqueue rollbackToSavepoint)
    canonicalRow : ∀ migration → NestedEffect (insertCanonical migration)
    schemaRow : ∀ migration schema → NestedEffect (insertAssociation migration schema)

  module Restricted = Restriction.Restricted Effect Reply NestedEffect

  abandonNested : ∀ problem → Restricted.Uses (abandon nested problem)
  abandonNested problem = Restricted.requested _ _ queued (λ _ → Restricted.returned _)

  publishNested : Restricted.Uses (publish nested)
  publishNested = Restricted.requested _ _ leaving (λ _ → Restricted.returned _)

  associationNested : ∀ migration schema → Restricted.Uses (association nested migration schema)
  associationNested migration schema = Restricted.requested _ _ (schemaRow migration schema) λ where
    (inj₁ problem) → abandonNested problem
    (inj₂ tt) → publishNested

  canonicalNested : ∀ migration schema → Restricted.Uses (canonical nested migration schema)
  canonicalNested migration schema = Restricted.requested _ _ (canonicalRow migration) λ where
    (inj₁ problem) → abandonNested problem
    (inj₂ tt) → associationNested migration schema

  recordNested : ∀ migration schema → Restricted.Uses (recordApplied nested migration schema)
  recordNested migration schema = Restricted.requested _ _ entering λ where
    (inj₁ problem) → Restricted.returned _
    (inj₂ tt) → canonicalNested migration schema

  finalCommandDoesNotRetry : ∀ context response events result →
    Runs (publish context) ((awaitCommand (finish context) , response) ∷ events) result →
    events ≡ [] × result ≡ response
  finalCommandDoesNotRetry _ _ _ _ (replied _ _ _ (returned _)) = refl , refl

  abortCannotSucceed : ∀ context problem events →
    Runs (abandon context problem) events (inj₂ tt) → ⊥
  abortCannotSucceed _ _ _ (replied _ _ tt ())

  publishSuccess : ∀ context events → Runs (publish context) events (inj₂ tt) →
    events ≡ (awaitCommand (finish context) , inj₂ tt) ∷ []
  publishSuccess _ _ (replied _ _ (inj₁ _) ())
  publishSuccess _ _ (replied _ _ (inj₂ tt) (returned _)) = refl

  associationSuccess : ∀ context migration schema events →
    Runs (association context migration schema) events (inj₂ tt) →
    events ≡ (insertAssociation migration schema , inj₂ tt) ∷
      (awaitCommand (finish context) , inj₂ tt) ∷ []
  associationSuccess context migration schema _ (replied _ _ (inj₁ problem) rest) =
    ⊥-elim (abortCannotSucceed context problem _ rest)
  associationSuccess context migration schema _ (replied _ _ (inj₂ tt) rest) =
    cong ((insertAssociation migration schema , inj₂ tt) ∷_) (publishSuccess context _ rest)

  canonicalSuccess : ∀ context migration schema events →
    Runs (canonical context migration schema) events (inj₂ tt) →
    events ≡ (insertCanonical migration , inj₂ tt) ∷
      (insertAssociation migration schema , inj₂ tt) ∷ (awaitCommand (finish context) , inj₂ tt) ∷ []
  canonicalSuccess context migration schema _ (replied _ _ (inj₁ problem) rest) =
    ⊥-elim (abortCannotSucceed context problem _ rest)
  canonicalSuccess context migration schema _ (replied _ _ (inj₂ tt) rest) =
    cong ((insertCanonical migration , inj₂ tt) ∷_) (associationSuccess context migration schema _ rest)

  successReceipts : ∀ context migration schema events →
    Runs (recordApplied context migration schema) events (inj₂ tt) →
    events ≡ (awaitCommand (enter context) , inj₂ tt) ∷
      (insertCanonical migration , inj₂ tt) ∷ (insertAssociation migration schema , inj₂ tt) ∷
      (awaitCommand (finish context) , inj₂ tt) ∷ []
  successReceipts context migration schema _ (replied _ _ (inj₁ _) ())
  successReceipts context migration schema _ (replied _ _ (inj₂ tt) rest) =
    cong ((awaitCommand (enter context) , inj₂ tt) ∷_) (canonicalSuccess context migration schema _ rest)
