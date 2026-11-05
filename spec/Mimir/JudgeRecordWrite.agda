{-# OPTIONS --safe #-}
-- Mimir supplies the persisted fields and enforces the limit on the actual
-- library-produced bytes. JSON serialization itself is a trusted operation.
module Mimir.JudgeRecordWrite where

import Mimir.OptionalLimit as Limit
open import Data.List using (List; length)
open import Data.Nat using (ℕ)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₂)
open import Data.Unit using (tt)
open import Mimir.Bits using (Byte)
open import Mimir.UnixPath using (Path)
open import Mimir.UUIDV4 using (Endian)
import Mimir.StandardLibrary as Library
import Mimir.JudgePersistence as Names
import Mimir.JudgeStateWire as Wire
import Mimir.JudgeStateBounds as Bounds
import Mimir.StructuredValue as JSON
import Mimir.JudgeNamedWrite as Named
module R = Wire.R

module Size (library : Library.Contract) (sizeMaximum : ℕ) where
  module B = Bounds.Size sizeMaximum
  module Encode = Wire.With library

  data Value : Names.Name → Set where
    report : ∀ value → B.ReportBounds value → Value Names.status
    incident : ∀ value → B.IncidentBounds value → Value Names.failure
    diagnostics : ∀ value → B.DiagnosticsBounds value → Value Names.diagnostics

  schema : ∀ {name} → Value name → JSON.Value
  schema (report value bounded) = Encode.report value
  schema (incident value bounded) = Encode.incident value
  schema (diagnostics value bounded) = Encode.diagnostics value

  bytes : ∀ {name} → Value name → List Byte
  bytes value = Library.Contract.compactJSON library (schema value)

  module With (Handle NativeError RandomError : Set) where
    module W = Named.With library Handle NativeError RandomError ⊥

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
