{-# OPTIONS --safe #-}
-- Kryzhen's ensure_schema as used on Mimir's Client. Catalog replies and
-- typed PostgreSQL values are inputs. Historical SQL bodies are identified,
-- not silently replaced by an assumption that they execute successfully.
module Mimir.MigrationBootstrap where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Integer using (ℤ; +_; -[1+_]; _≤_; _<_; _≤?_; _<?_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.Effects as Effects

data SelfMigration : Set where setup canonicalRows perSchemaRows : SelfMigration

version : SelfMigration → ℤ
version setup = + 0
version canonicalRows = + 1
version perSchemaRows = + 2

selfMigrations : List SelfMigration
selfMigrations = setup ∷ canonicalRows ∷ perSchemaRows ∷ []

module Bootstrap (Problem Schema SearchPath : Set) where
  Result : Set → Set
  Result A = Problem ⊎ A

  data Statement : Set where
    dropLegacyLedger createVersionLedger stampZeroAndOne : Statement
    executeSelf stampVersion : SelfMigration → Statement
    restoreSearchPath : SearchPath → Statement
    backfillAssociations : Schema → Statement

  data Effect : Set where
    currentSchema searchPath legacySingletonColumn ledgerExists canonicalExists maxVersion : Effect
    beginTransaction commitTransaction enqueueRollback : Effect
    statement : Statement → Effect

  Reply : Effect → Set
  Reply currentSchema = Result Schema
  Reply searchPath = Result SearchPath
  Reply legacySingletonColumn = Result Bool
  Reply ledgerExists = Result Bool
  Reply canonicalExists = Result Bool
  Reply maxVersion = Result (Maybe ℤ)
  Reply enqueueRollback = ⊤
  Reply _ = Result ⊤

  module E = Effects.Protocol Effect Reply
  open E public

  abandon : Problem → Script (Result ⊤)
  abandon problem = ask enqueueRollback (λ _ → done (inj₁ problem))

  statements : List Statement → Script (Result ⊤)
  statements [] = done (inj₂ tt)
  statements (instruction ∷ rest) = ask (statement instruction) λ where
    (inj₁ problem) → done (inj₁ problem)
    (inj₂ tt) → statements rest

  entered : List Statement → Script (Result ⊤)
  entered body = statements body >>= λ where
    (inj₁ problem) → abandon problem
    (inj₂ tt) → ask commitTransaction done

  transaction : List Statement → Script (Result ⊤)
  transaction body = ask beginTransaction λ where
    (inj₁ problem) → done (inj₁ problem)
    (inj₂ tt) → entered body

  legacyBody : List Statement
  legacyBody = dropLegacyLedger ∷ createVersionLedger ∷ stampVersion setup ∷
    stampVersion canonicalRows ∷ stampVersion perSchemaRows ∷ []

  migrateLegacy : Script (Result ⊤)
  migrateLegacy = ask legacySingletonColumn λ where
    (inj₁ problem) → done (inj₁ problem)
    (inj₂ false) → done (inj₂ tt)
    (inj₂ true) → transaction legacyBody

  defaultVersion : Maybe ℤ → ℤ
  defaultVersion nothing = -[1+ 0 ]
  defaultVersion (just value) = value

  -- This branch is deliberately not wrapped in a transaction: the source
  -- creates the version table and stamps 0/1 in separate awaited statements.
  bootstrapWithoutLedger : Script (Result ℤ)
  bootstrapWithoutLedger = ask canonicalExists λ where
    (inj₁ problem) → done (inj₁ problem)
    (inj₂ false) → done (inj₂ -[1+ 0 ])
    (inj₂ true) → statements (createVersionLedger ∷ stampZeroAndOne ∷ []) >>= λ where
      (inj₁ problem) → done (inj₁ problem)
      (inj₂ tt) → done (inj₂ (+ 1))

  currentVersion : Script (Result ℤ)
  currentVersion = ask ledgerExists λ where
    (inj₁ problem) → done (inj₁ problem)
    (inj₂ false) → bootstrapWithoutLedger
    (inj₂ true) → ask maxVersion λ where
      (inj₁ problem) → done (inj₁ problem)
      (inj₂ value) → done (inj₂ (defaultVersion value))

  upgrades : ℤ → List SelfMigration → Script (Result ⊤)
  upgrades current [] = done (inj₂ tt)
  upgrades current (migration ∷ rest) with version migration ≤? current
  ... | yes already = upgrades current rest
  ... | no missing = transaction (executeSelf migration ∷ stampVersion migration ∷ []) >>= λ where
    (inj₁ problem) → done (inj₁ problem)
    (inj₂ tt) → upgrades (version migration) rest

  afterRestore : ℤ → Schema → Script (Result ⊤)
  afterRestore before schema with before <? version perSchemaRows
  ... | yes newlyReached = ask (statement (backfillAssociations schema)) done
  ... | no already = done (inj₂ tt)

  restore : ℤ → Schema → SearchPath → Script (Result ⊤)
  restore before schema path = ask (statement (restoreSearchPath path)) λ where
    (inj₁ problem) → done (inj₁ problem)
    (inj₂ tt) → afterRestore before schema

  upgradeThenRestore : ℤ → Schema → SearchPath → Script (Result ⊤)
  upgradeThenRestore before schema path = upgrades before selfMigrations >>= λ where
    (inj₁ problem) → done (inj₁ problem)
    (inj₂ tt) → restore before schema path

  body : Schema → SearchPath → Script (Result ⊤)
  body schema path = migrateLegacy >>= λ where
    (inj₁ problem) → done (inj₁ problem)
    (inj₂ tt) → currentVersion >>= λ where
      (inj₁ problem) → done (inj₁ problem)
      (inj₂ before) → upgradeThenRestore before schema path

  capturePath : Schema → Script (Result ⊤)
  capturePath schema = ask searchPath λ where
    (inj₁ problem) → done (inj₁ problem)
    (inj₂ path) → body schema path

  ensureSchema : Script (Result ⊤)
  ensureSchema = ask currentSchema λ where
    (inj₁ problem) → done (inj₁ problem)
    (inj₂ schema) → capturePath schema

  pathReadFailureCannotChangeSchema : ∀ schema problem events result →
    Runs (capturePath schema) ((searchPath , inj₁ problem) ∷ events) result →
    events ≡ [] × result ≡ inj₁ problem
  pathReadFailureCannotChangeSchema _ _ _ _ (replied _ _ _ (returned _)) = refl , refl

  failedRestoreCannotBackfill : ∀ before schema path problem events result →
    Runs (restore before schema path) ((statement (restoreSearchPath path) , inj₁ problem) ∷ events) result →
    events ≡ [] × result ≡ inj₁ problem
  failedRestoreCannotBackfill _ _ _ _ _ _ (replied _ _ _ (returned _)) = refl , refl

  failedStatementStopsBody : ∀ instruction rest problem events result →
    Runs (statements (instruction ∷ rest)) ((statement instruction , inj₁ problem) ∷ events) result →
    events ≡ [] × result ≡ inj₁ problem
  failedStatementStopsBody _ _ _ _ _ (replied _ _ _ (returned _)) = refl , refl

  absentLegacyOnlyChecksCatalog : ∀ events result →
    Runs migrateLegacy ((legacySingletonColumn , inj₂ false) ∷ events) result →
    events ≡ [] × result ≡ inj₂ tt
  absentLegacyOnlyChecksCatalog _ _ (replied _ _ _ (returned _)) = refl , refl
