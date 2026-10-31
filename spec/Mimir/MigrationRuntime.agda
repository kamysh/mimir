{-# OPTIONS --safe #-}
-- Concrete composition of Mimir's migration driver, row decoder, legacy
-- importer, bootstrap and ledger-write protocols. Loader/receipt parsing and
-- the source planner are explicit remaining inputs, not correctness axioms.
module Mimir.MigrationRuntime where

open import Data.Bool using (Bool)
open import Data.List using (List; map)
open import Data.Product using (proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Data.String using (toList)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.Collections using (module Equality)
import Mimir.Effects as Effects
import Mimir.EffectExpansion as Expansion
import Mimir.MigrationDriver as Driver
import Mimir.MigrationLedger as Ledger
import Mimir.MigrationLedgerWrite as LedgerWrite
import Mimir.MigrationBootstrap as Bootstrap
import Mimir.MigrationRows as Rows
import Mimir.MigrationImportValues as ImportValues

mapError : ∀ {From To A : Set} → (From → To) → From ⊎ A → To ⊎ A
mapError convert (inj₁ error) = inj₁ (convert error)
mapError convert (inj₂ value) = inj₂ value

module Runtime (NativeProblem PlanProblem : Set) where
  data DatabaseProblem : Set where
    native : NativeProblem → DatabaseProblem
    corruptChecksum : Rows.Error → DatabaseProblem

  module ConcreteImport = ImportValues.Concrete DatabaseProblem
  module I = ConcreteImport.I
  module B = Bootstrap.Bootstrap DatabaseProblem Text Text
  module L = LedgerWrite.Write DatabaseProblem Ledger.Migration Text
  module Names = Equality Text _≟Text_

  data Problem : Set where
    database : DatabaseProblem → Problem
    duplicateName checksumMismatch : Text → Problem
    invalidPlan : PlanProblem → Problem
    legacyImport : I.Error → Problem

  module D = Driver.Driver Problem Ledger.Migration ImportValues.Receipt Rows.Checksums.Table (List Text)

  record Inputs : Set where
    field
      embedded : DatabaseProblem ⊎ List Ledger.Migration
      receipt : DatabaseProblem ⊎ ImportValues.Receipt
      planner : List Ledger.Migration → PlanProblem ⊎ List Ledger.Migration
  open Inputs

  pure : Inputs → D.Pure
  pure inputs = record
    { embedded = mapError database (embedded inputs)
    ; decodeReceipt = mapError database (receipt inputs)
    ; checkNames = λ migrations → mapError duplicateName (Rows.checkNames migrations)
    ; order = λ migrations → mapError invalidPlan (planner inputs migrations)
    ; checkChecksums = λ migrations checksums → mapError checksumMismatch (Rows.checkChecksums migrations checksums)
    ; contains = λ snapshot migration → does (Names.present? (Ledger.Migration.name migration) snapshot)
    }

  data Effect : Set where
    connect acquireLock releaseLock dropConnection : Effect
    readChecksumRows readPublicNames : Effect
    beginTransaction commitTransaction enqueueRollback : Effect
    executeScript : Text → Effect
    bootstrap : B.Effect → Effect
    ledger : L.Effect → Effect
    legacyExists readLegacyRows currentSchema : Effect

  Reply : Effect → Set
  Reply readChecksumRows = DatabaseProblem ⊎ List Rows.RawRow
  Reply readPublicNames = DatabaseProblem ⊎ List Text
  Reply dropConnection = ⊤
  Reply enqueueRollback = ⊤
  Reply (bootstrap operation) = B.Reply operation
  Reply (ledger operation) = L.Reply operation
  Reply legacyExists = DatabaseProblem ⊎ Bool
  Reply readLegacyRows = DatabaseProblem ⊎ List ImportValues.DatabaseRow
  Reply currentSchema = DatabaseProblem ⊎ Text
  Reply _ = DatabaseProblem ⊎ ⊤

  module E = Effects.Protocol Effect Reply

  convertError : ∀ {From To A : Set} → (From → To) → E.Script (From ⊎ A) → E.Script (To ⊎ A)
  convertError convert program = program E.>>= (λ result → E.done (mapError convert result))

  module BootstrapExpansion = Expansion.Expand B.Effect B.Reply Effect Reply
  bootstrapOperation : (operation : B.Effect) → E.Script (B.Reply operation)
  bootstrapOperation operation = E.ask (bootstrap operation) E.done
  module EmbeddedBootstrap = BootstrapExpansion.With bootstrapOperation

  module LedgerExpansion = Expansion.Expand L.Effect L.Reply Effect Reply
  ledgerOperation : (operation : L.Effect) → E.Script (L.Reply operation)
  ledgerOperation operation = E.ask (ledger operation) E.done
  module EmbeddedLedger = LedgerExpansion.With ledgerOperation

  checksumRows : E.Script (DatabaseProblem ⊎ Rows.Checksums.Table)
  checksumRows = E.ask readChecksumRows λ where
    (inj₁ problem) → E.done (inj₁ problem)
    (inj₂ rows) → E.done (mapError corruptChecksum (Rows.loadApplied rows))

  loadedNames : List Rows.RawRow → Rows.Error ⊎ Rows.Checksums.Table → DatabaseProblem ⊎ List Text
  loadedNames rows (inj₁ error) = inj₁ (corruptChecksum error)
  loadedNames rows (inj₂ checked) = inj₂ (map proj₁ rows)

  canonicalNames : E.Script (DatabaseProblem ⊎ List Text)
  canonicalNames = E.ask readChecksumRows λ where
    (inj₁ problem) → E.done (inj₁ problem)
    (inj₂ rows) → E.done (loadedNames rows (Rows.loadApplied rows))

  importOperation : (operation : I.Effect) → E.Script (I.Reply operation)
  importOperation I.legacyExists = E.ask legacyExists (λ result → E.done (mapError I.external result))
  importOperation I.readSuccessfulRows = E.ask readLegacyRows λ where
    (inj₁ problem) → E.done (inj₁ (I.external problem))
    (inj₂ rows) → E.done (inj₂ (ImportValues.rows rows))
  importOperation I.ensureSchema = convertError I.external (EmbeddedBootstrap.expand B.ensureSchema)
  importOperation I.readCanonicalNames = convertError I.external canonicalNames
  importOperation I.currentSchema = E.ask currentSchema (λ result → E.done (mapError I.external result))
  importOperation I.dropLegacyTable = E.ask (executeScript (toList "DROP TABLE IF EXISTS _sqlx_migrations"))
    (λ result → E.done (mapError I.external result))
  importOperation (I.recordApplied migration schema) =
    convertError I.external (EmbeddedLedger.expand (L.recordApplied LedgerWrite.standalone migration schema))

  module ImportExpansion = Expansion.Expand I.Effect I.Reply Effect Reply
  module EmbeddedImport = ImportExpansion.With importOperation

  importLegacy : ImportValues.Receipt → List Ledger.Migration → E.Script (Problem ⊎ ⊤)
  importLegacy receiptValue migrations = convertError legacyImport
    (EmbeddedImport.expand (Program.start (ImportValues.Receipt.entries receiptValue)))
    where module Program = I.Run (ConcreteImport.pure migrations)

  implementation : (operation : D.Effect) → E.Script (D.Reply operation)
  implementation D.connect = E.ask connect (λ result → E.done (mapError database result))
  implementation D.acquireLock = E.ask acquireLock (λ result → E.done (mapError database result))
  implementation D.releaseLock = E.ask releaseLock (λ result → E.done (mapError database result))
  implementation D.dropConnection = E.ask dropConnection E.done
  implementation D.ensureSchema = convertError database (EmbeddedBootstrap.expand B.ensureSchema)
  implementation D.loadChecksums = convertError database checksumRows
  implementation D.loadAppliedForPublic = E.ask readPublicNames (λ result → E.done (mapError database result))
  implementation D.beginTransaction = E.ask beginTransaction (λ result → E.done (mapError database result))
  implementation D.setLocalSearchPath =
    E.ask (executeScript (toList "SET LOCAL search_path TO public,ag_catalog"))
      (λ result → E.done (mapError database result))
  implementation D.commitTransaction = E.ask commitTransaction (λ result → E.done (mapError database result))
  implementation D.enqueueRollback = E.ask enqueueRollback E.done
  implementation (D.executeOriginalSQL migration) =
    E.ask (executeScript (Ledger.Metadata.script (Ledger.Migration.payload migration)))
      (λ result → E.done (mapError database result))
  implementation (D.recordBothLedgerRows migration) = convertError database
    (EmbeddedLedger.expand (L.recordApplied LedgerWrite.nested migration (toList "public")))
  implementation (D.importLegacy receiptValue migrations) = importLegacy receiptValue migrations

  module DriverExpansion = Expansion.Expand D.Effect D.Reply Effect Reply
  module Expanded = DriverExpansion.With implementation

  module Run (inputs : Inputs) where
    module Source = D.Run (pure inputs)
    migrate : E.Script (Problem ⊎ ⊤)
    migrate = Expanded.expand Source.start
