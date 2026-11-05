{-# OPTIONS --safe #-}
-- Actual persisted record serializers are composed with the named-write
-- protocol. Unicode and native numeric domains are explicit input evidence.
module Mimir.JudgeRecordWrite where

import Mimir.OptionalLimit as Limit
open import Data.List using (List; length)
open import Data.Nat using (ℕ; _≤_)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Mimir.Bits using (Byte)
open import Mimir.UnixPath using (Path)
open import Mimir.UUIDV4 using (Endian)
import Mimir.JudgePersistence as Names
import Mimir.JudgeStateWire as Wire
import Mimir.JudgeStateText as Text
import Mimir.JudgeStateBounds as Bounds
import Mimir.JudgeStateSerialize as Serialize
import Mimir.JsonCompactRecords as Compact
import Mimir.StructuredValue as JSON
import Mimir.JudgeNamedWrite as Named
module R = Wire.R

module Size (sizeMaximum : ℕ) where
  module B = Bounds.Size sizeMaximum

  data Value : Names.Name → Set where
    report : ∀ value → B.ReportBounds value → Text.ReportText value → Value Names.status
    incident : ∀ value → B.IncidentBounds value → Text.IncidentText value → Value Names.failure
    diagnostics : ∀ value → B.DiagnosticsBounds value → Text.DiagnosticsText value → Value Names.diagnostics

  schema : ∀ {name} → Value name → JSON.Value
  schema (report value bounded valid) = Wire.report value
  schema (incident value bounded valid) = Wire.incident value
  schema (diagnostics value bounded valid) = Wire.diagnostics value

  supported : ∀ {name} (value : Value name) → Compact.Supported (schema value)
  supported (report value bounded valid) = Serialize.report value valid
  supported (incident value bounded valid) = Serialize.incident value valid
  supported (diagnostics value bounded valid) = Serialize.diagnostics value valid

  bytes : ∀ {name} → Value name → List Byte
  bytes value = Compact.bytes (schema value) (supported value)

  exactSize : ∀ {name} (value : Value name) →
    length (bytes value) ≡ Compact.count (schema value) (supported value)
  exactSize value = Compact.exactCount (schema value) (supported value)

  module With (Handle NativeError RandomError : Set) where
    module W = Named.With Handle NativeError RandomError ⊥

    write : ∀ {name} → Path → Endian → Value name → W.P.Script W.Outcome
    write {name} directory endian value = W.writeBytes directory name endian (bytes value)

    successFits : ∀ {name} directory endian (value : Value name) {events} →
      W.P.Runs (write directory endian value) events (W.returned (inj₂ tt)) →
      Limit.Within (Names.limit name) (length (bytes value))
    successFits {name} directory endian value run = W.successRequiresBound directory name endian (bytes value) run

    successReceipts : ∀ {name} directory endian (value : Value name) {events} →
      W.P.Runs (write directory endian value) events (W.returned (inj₂ tt)) →
      W.Committed directory name endian (bytes value) events
    successReceipts {name} directory endian value run = W.successRequiresReceipts directory name endian (bytes value) run
