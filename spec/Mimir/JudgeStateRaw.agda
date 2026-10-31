{-# OPTIONS --safe #-}
-- Concrete raw readers for all persisted judge record families. Field names,
-- order, carriers, defaults and builders come from JudgeStateDecode. Native
-- correspondence and full independent acceptance/error equivalence remain
-- obligations; typing these definitions does not discharge them.
import Mimir.FloatConversion
module Mimir.JudgeStateRaw (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.List using (List; [])
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
import Mimir.SerdeSequence as Sequence
import Mimir.SerdeSlots as Slots
import Mimir.SerdeFlow as Flow
import Mimir.SerdeRecord as RecordDependency
private
  module Record = RecordDependency floatConversion
import Mimir.SerdeVector as VectorDependency
private
  module Vector = VectorDependency floatConversion
import Mimir.SerdeOption as OptionDependency
private
  module Option = OptionDependency floatConversion
import Mimir.JudgeStateAtoms as AtomsDependency
private
  module Atoms = AtomsDependency floatConversion
import Mimir.JudgeStateDecode as Decode
import Mimir.JudgeStatePrimitives as P
import Mimir.SignedMachine as Machine
import Mimir.UUIDGroups as UUID
import Mimir.SourceFailure as Source
import Mimir.Validation as V

recordExpected : V.Fault
recordExpected = V.fault [] V.malformedInput "expected state record"

arrayExpected : V.Fault
arrayExpected = V.fault [] V.malformedInput "expected an array"

module Parser (checks : Machine.OverflowChecks) (sizeMaximum : ℕ) where
  module D = Decode.Size sizeMaximum
  module A = Atoms.Parser checks
  module R = Decode.R

  readRecord : ∀ {Value} (fields : List Sequence.Field) → (Sequence.Values fields → Value) →
    (ℕ → Slots.Readers fields) → ℕ → Flow.Parser Value
  readRecord fields build readers allowance input = Flow.mapProductive
    (λ values → build (Slots.toSequence fields values))
    (Record.Parser.read checks fields readers recordExpected allowance input)

  vector : ∀ {Value} → (ℕ → Flow.Parser Value) → ℕ → Flow.Parser (List Value)
  vector {Value} child = Vector.Parser.read checks Value child arrayExpected

  size : Flow.Parser ℕ
  size = A.readUint sizeMaximum

  u64 : Flow.Parser ℕ
  u64 = A.readUint P.u64Maximum

  uuidVector : ℕ → Flow.Parser (List UUID.UUID)
  uuidVector = vector (λ allowance → A.readUUID)

  sourceReaders : ℕ → Slots.Readers D.sourceFields
  sourceReaders allowance = A.readText , A.readText , size , size , A.readText , tt

  source : ℕ → Flow.Parser Source.Failure
  source = readRecord D.sourceFields D.buildSource sourceReaders

  deferredReaders : ℕ → Slots.Readers D.deferredFields
  deferredReaders allowance = A.readUUID , A.readSigned , tt

  deferred : ℕ → Flow.Parser R.Deferred
  deferred = readRecord D.deferredFields D.buildDeferred deferredReaders

  diagnosticReaders : ℕ → Slots.Readers D.diagnosticFields
  diagnosticReaders allowance = u64 , A.readUUID , A.readText , A.readText , tt

  diagnostic : ℕ → Flow.Parser R.FailureDiagnostic
  diagnostic = readRecord D.diagnosticFields D.buildDiagnostic diagnosticReaders

  reportReaders : ℕ → Slots.Readers D.reportFields
  reportReaders allowance =
    A.readText ,
    Option.read A.readText ,
    Option.read (diagnostic allowance) ,
    Option.read A.readText ,
    Option.read (source allowance) ,
    Option.read A.readUUID ,
    uuidVector allowance ,
    size , size , size , size , size ,
    vector deferred allowance ,
    A.readText , u64 , tt

  report : ℕ → Flow.Parser R.Report
  report = readRecord D.reportFields D.buildReport reportReaders

  confirmedReaders : ℕ → Slots.Readers D.confirmedFields
  confirmedReaders allowance = A.readUUID , u64 , tt

  confirmed : ℕ → Flow.Parser R.Confirmed
  confirmed = readRecord D.confirmedFields D.buildConfirmed confirmedReaders

  incidentReaders : ℕ → Slots.Readers D.incidentFields
  incidentReaders allowance = report allowance , Option.read (report allowance) ,
    vector confirmed allowance , Option.read u64 , tt

  incident : ℕ → Flow.Parser R.Incident
  incident = readRecord D.incidentFields D.buildIncident incidentReaders

  eventReaders : ℕ → Slots.Readers D.eventFields
  eventReaders allowance = u64 , A.readUUID , A.readText , size , size ,
    Option.read A.readText , Option.read A.readText , Option.read size , tt

  event : ℕ → Flow.Parser R.Event
  event = readRecord D.eventFields D.buildEvent eventReaders

  traceReaders : ℕ → Slots.Readers D.traceFields
  traceReaders allowance = A.readUUID , u64 , Option.read u64 , A.readText ,
    Option.read A.readText , uuidVector allowance , size , size ,
    vector event allowance , size , tt

  trace : ℕ → Flow.Parser R.Trace
  trace = readRecord D.traceFields D.buildTrace traceReaders

  diagnosticsReaders : ℕ → Slots.Readers D.diagnosticsFields
  diagnosticsReaders allowance = vector trace allowance , tt

  diagnostics : ℕ → Flow.Parser R.Diagnostics
  diagnostics = readRecord D.diagnosticsFields D.buildDiagnostics diagnosticsReaders
