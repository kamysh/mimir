{-# OPTIONS --safe #-}
-- Expansion of db.rs's ledger operation into Kryzhen's nested savepoint.
-- The remaining database operations are still explicit protocol boundaries.
module Mimir.MigrationComposition where

open import Data.List using (List)
open import Data.Product using (Σ; _×_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.Effects as Effects
import Mimir.EffectExpansion as Expansion
import Mimir.MigrationDriver as Driver
import Mimir.MigrationLedgerWrite as Ledger
import Mimir.MigrationBootstrap as Bootstrap

module Compose (Problem Migration Receipt Checksums Snapshot Schema SearchPath : Set)
  (publicSchema : Schema) where
  module D = Driver.Driver Problem Migration Receipt Checksums Snapshot
  module L = Ledger.Write Problem Migration Schema
  module B = Bootstrap.Bootstrap Problem Schema SearchPath

  data Effect : Set where
    driver : D.Effect → Effect
    ledger : L.Effect → Effect
    bootstrap : B.Effect → Effect

  Reply : Effect → Set
  Reply (driver operation) = D.Reply operation
  Reply (ledger operation) = L.Reply operation
  Reply (bootstrap operation) = B.Reply operation

  module E = Effects.Protocol Effect Reply
  module LiftLedger = Expansion.Expand L.Effect L.Reply Effect Reply

  ledgerOperation : (operation : L.Effect) → E.Script (L.Reply operation)
  ledgerOperation operation = E.ask (ledger operation) E.done

  module EmbeddedLedger = LiftLedger.With ledgerOperation

  module LiftBootstrap = Expansion.Expand B.Effect B.Reply Effect Reply

  bootstrapOperation : (operation : B.Effect) → E.Script (B.Reply operation)
  bootstrapOperation operation = E.ask (bootstrap operation) E.done

  module EmbeddedBootstrap = LiftBootstrap.With bootstrapOperation

  implementation : (operation : D.Effect) → E.Script (D.Reply operation)
  implementation (D.recordBothLedgerRows migration) =
    EmbeddedLedger.expand (L.recordApplied Ledger.nested migration publicSchema)
  implementation D.connect = E.ask (driver D.connect) E.done
  implementation D.acquireLock = E.ask (driver D.acquireLock) E.done
  implementation D.ensureSchema = EmbeddedBootstrap.expand B.ensureSchema
  implementation D.loadChecksums = E.ask (driver D.loadChecksums) E.done
  implementation D.loadAppliedForPublic = E.ask (driver D.loadAppliedForPublic) E.done
  implementation D.beginTransaction = E.ask (driver D.beginTransaction) E.done
  implementation D.setLocalSearchPath = E.ask (driver D.setLocalSearchPath) E.done
  implementation D.commitTransaction = E.ask (driver D.commitTransaction) E.done
  implementation D.enqueueRollback = E.ask (driver D.enqueueRollback) E.done
  implementation D.releaseLock = E.ask (driver D.releaseLock) E.done
  implementation D.dropConnection = E.ask (driver D.dropConnection) E.done
  implementation (D.importLegacy receipt migrations) =
    E.ask (driver (D.importLegacy receipt migrations)) E.done
  implementation (D.executeOriginalSQL migration) =
    E.ask (driver (D.executeOriginalSQL migration)) E.done

  module Refine = Expansion.Expand D.Effect D.Reply Effect Reply
  module Expanded = Refine.With implementation

  ledgerIsNested : ∀ migration → implementation (D.recordBothLedgerRows migration) ≡
    EmbeddedLedger.expand (L.recordApplied Ledger.nested migration publicSchema)
  ledgerIsNested migration = refl

  module Run (pure : D.Pure) where
    module Source = D.Run pure

    migrate : E.Script (D.Result ⊤)
    migrate = Expanded.expand Source.start

    everyExecutionProjects : ∀ {events result} → E.Runs migrate events result →
      Σ (List D.Event) λ abstractEvents →
        D.Runs Source.start abstractEvents result × Expanded.Translation abstractEvents events
    everyExecutionProjects = Expanded.reflectRun Source.start
