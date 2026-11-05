{-# OPTIONS --safe #-}
-- File-level decoding for the three persisted judge names. The native depth
-- allowance and whitespace-only suffix rule are fixed at this boundary.
import Mimir.FloatConversion
module Mimir.JudgeStateDocument (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.List using ([])
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Mimir.JudgePersistence as Names
import Mimir.JudgeStateWire as Wire
import Mimir.JudgeStateRaw as RawDependency
private
  module Raw = RawDependency floatConversion
import Mimir.SerdeDocument as DocumentDependency
private
  module Document = DocumentDependency floatConversion
import Mimir.SerdeFlow as Flow
import Mimir.SignedMachine as Machine
module R = Wire.R

Value : Names.Name → Set
Value Names.status = R.Report
Value Names.failure = R.Incident
Value Names.diagnostics = R.Diagnostics

module Parser (checks : Machine.OverflowChecks) (sizeMaximum : ℕ) where
  module D = Document.Parser checks
  module P = Raw.Parser checks sizeMaximum

  recordReader : (name : Names.Name) → ℕ → Flow.Parser (Value name)
  recordReader Names.status = P.report
  recordReader Names.failure = P.incident
  recordReader Names.diagnostics = P.diagnostics

  read : (name : Names.Name) → Flow.Parser (Value name)
  read name = D.read (recordReader name 127)

  successExhausts : ∀ name input value position →
    Flow.Productive.result (read name input) ≡ Flow.ordinary (Flow.F.success value position) →
    Flow.F.Cursor.remaining position ≡ []
  successExhausts name input value position observed = D.successExhausts (recordReader name 127) input value position observed
