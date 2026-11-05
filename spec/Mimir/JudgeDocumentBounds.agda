{-# OPTIONS --safe #-}
-- Numeric invariants reach complete document results.
import Mimir.FloatConversion
module Mimir.JudgeDocumentBounds (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Mimir.JudgePersistence as Names
import Mimir.JudgeStateBounds as Bounds
import Mimir.JudgeStateDocument as DocumentDependency
private
  module Document = DocumentDependency floatConversion
import Mimir.JudgeRawCompositeBounds as RawDependency
private
  module Raw = RawDependency floatConversion
import Mimir.SerdeDocumentInvariant as InvariantDependency
private
  module Invariant = InvariantDependency floatConversion
import Mimir.SerdeFlow as Flow
import Mimir.SerdeSuccess as S
import Mimir.SignedMachine as Machine

module Size (sizeMaximum : ℕ) where
  private
    module B = Bounds.Size sizeMaximum

  Valid : (name : Names.Name) → Document.Value name → Set
  Valid Names.status = B.ReportBounds
  Valid Names.failure = B.IncidentBounds
  Valid Names.diagnostics = B.DiagnosticsBounds

module Parser (checks : Machine.OverflowChecks) (sizeMaximum : ℕ) where
  private
    module B = Size sizeMaximum
  private
    module D = Document.Parser checks sizeMaximum
  private
    module R = Raw.Parser checks sizeMaximum
  private
    module I = Invariant.Parser checks

  recordReader : ∀ name allowance input → S.Ensures (B.Valid name)
    (Flow.Productive.result (D.recordReader name allowance input))
  recordReader Names.status allowance input = R.report allowance input
  recordReader Names.failure allowance input = R.incident allowance input
  recordReader Names.diagnostics allowance input = R.diagnostics allowance input

  read : ∀ name input → S.Ensures (B.Valid name)
    (Flow.Productive.result (D.read name input))
  read name input = I.read (D.recordReader name 127) (B.Valid name)
    (recordReader name 127) input

  successful : ∀ name input value position →
    Flow.Productive.result (D.read name input) ≡ Flow.ordinary (Flow.F.success value position) →
    B.Valid name value
  successful name input value position observed = S.extract (B.Valid name)
    (Flow.Productive.result (D.read name input)) value position
    (read name input) observed

