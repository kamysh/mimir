{-# OPTIONS --safe #-}
-- Connect the concrete ordered-file loader to migration startup. File errors
-- are returned before connecting, locking, importing or issuing any SQL.
module Mimir.MigrationFileRuntime where

open import Data.List using (List; [])
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
import Mimir.MigrationRuntime as Runtime
import Mimir.MigrationFileParsing as Files
import Mimir.MigrationLedger as Ledger
import Mimir.MigrationImportValues as Import

module WithExternal (NativeProblem PlanProblem : Set) where
  module R = Runtime.Runtime (Files.Error ⊎ NativeProblem) PlanProblem

  inputs : List Files.File → R.DatabaseProblem ⊎ Import.Receipt →
    (List Ledger.Migration → PlanProblem ⊎ List Ledger.Migration) → R.Inputs
  inputs files receipt planner = record
    { embedded = Runtime.mapError (λ problem → R.native (inj₁ problem)) (Files.loadOrdered files)
    ; receipt = receipt
    ; planner = planner
    }

  migrate : List Files.File → R.DatabaseProblem ⊎ Import.Receipt →
    (List Ledger.Migration → PlanProblem ⊎ List Ledger.Migration) → R.E.Script (R.Problem ⊎ ⊤)
  migrate files receipt planner = R.Run.migrate (inputs files receipt planner)

  loadFailureBeforeEffects : ∀ files receipt planner problem → Files.loadOrdered files ≡ inj₁ problem →
    migrate files receipt planner ≡ R.E.done (inj₁ (R.database (R.native (inj₁ problem))))
  loadFailureBeforeEffects files receipt planner problem failed rewrite failed = refl

  noEventsAfterLoadFailure : ∀ files receipt planner problem → Files.loadOrdered files ≡ inj₁ problem →
    ∀ events result → R.E.Runs (migrate files receipt planner) events result →
    events ≡ [] × result ≡ inj₁ (R.database (R.native (inj₁ problem)))
  noEventsAfterLoadFailure files receipt planner problem failed events result execution =
    R.E.completedCannotProduceEffects (subst (λ program → R.E.Runs program events result)
      (loadFailureBeforeEffects files receipt planner problem failed) execution)
