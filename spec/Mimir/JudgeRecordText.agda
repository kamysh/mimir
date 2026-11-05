{-# OPTIONS --safe #-}
-- All persisted textual fields are Unicode-valid in successful read receipts.
import Mimir.FloatConversion
module Mimir.JudgeRecordText (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Mimir.JudgePersistence as Names
import Mimir.JudgeStateText as Text
import Mimir.JudgeStateDocument as DocumentDependency
private
  module Document = DocumentDependency floatConversion
import Mimir.JudgeRawText as RawDependency
private
  module Raw = RawDependency floatConversion
import Mimir.JudgeRecordRead as RecordReadDependency
private
  module RecordRead = RecordReadDependency floatConversion
import Mimir.SerdeDocumentInvariant as InvariantDependency
private
  module Invariant = InvariantDependency floatConversion
import Mimir.SerdeFlow as Flow
import Mimir.SerdeSuccess as S
import Mimir.SignedMachine as Machine

Valid : (name : Names.Name) → Document.Value name → Set
Valid Names.status = Text.ReportText
Valid Names.failure = Text.IncidentText
Valid Names.diagnostics = Text.DiagnosticsText

module Parser (checks : Machine.OverflowChecks) (sizeMaximum : ℕ) where
  private
    module D = Document.Parser checks sizeMaximum
    module R = Raw.Parser checks sizeMaximum
    module I = Invariant.Parser checks

  recordReader : ∀ name allowance input → S.Ensures (Valid name)
    (Flow.Productive.result (D.recordReader name allowance input))
  recordReader Names.status allowance input = R.report allowance input
  recordReader Names.failure allowance input = R.incident allowance input
  recordReader Names.diagnostics allowance input = R.diagnostics allowance input

  read : ∀ name input → S.Ensures (Valid name)
    (Flow.Productive.result (D.read name input))
  read name input = I.read (D.recordReader name 127) (Valid name)
    (recordReader name 127) input

  successful : ∀ name input value position →
    Flow.Productive.result (D.read name input) ≡ Flow.ordinary (Flow.F.success value position) →
    Valid name value
  successful name input value position observed = S.extract (Valid name) (Flow.Productive.result (D.read name input))
    value position (read name input) observed

module With (Handle NativeError : Set) (checks : Machine.OverflowChecks) (sizeMaximum : ℕ) where
  loaded : ∀ name (accepted : RecordRead.With.Named.R.Loaded Handle NativeError checks sizeMaximum name (Names.limit name)) →
    Valid name (RecordRead.With.Named.R.Loaded.value accepted)
  loaded name accepted = Parser.successful checks sizeMaximum name
    (RecordRead.With.Named.R.Raw.Read.bytes {checks = checks}
     {sizeMaximum = sizeMaximum} {name = name}
     (RecordRead.With.Named.R.Loaded.raw accepted))
    (RecordRead.With.Named.R.Loaded.value accepted)
    (RecordRead.With.Named.R.Loaded.position accepted)
    (RecordRead.With.Named.R.Loaded.decoded accepted)
