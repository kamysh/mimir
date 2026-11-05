{-# OPTIONS --safe #-}
-- Concrete numeric invariants for the source and deferred-review records.
-- Text and UUID fields have no additional numeric restriction here.
import Mimir.FloatConversion
module Mimir.JudgeRawLeafBounds (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Fin using (zero; suc)
open import Data.Nat using (ℕ; _≤_; z≤n)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Unit using (⊤; tt)
import Mimir.SerdeSlots as Slots
import Mimir.SerdeSlotInvariant as I
import Mimir.SerdeSuccess as S
import Mimir.SerdeFlow as Flow
import Mimir.JudgeRawInvariant as InvariantDependency
private
  module Invariant = InvariantDependency floatConversion
import Mimir.JudgeStateRaw as RawDependency
private
  module Raw = RawDependency floatConversion
import Mimir.JudgeStateBounds as Bounds
import Mimir.JudgeStatePrimitives as P
import Mimir.SignedMachine as Machine

module Parser (checks : Machine.OverflowChecks) (sizeMaximum : ℕ) where
  private
    module R = Raw.Parser checks sizeMaximum
  private
    module D = R.D
  private
    module B = Bounds.Size sizeMaximum
  private
    module Inv = Invariant.Parser checks sizeMaximum

  sourceProperties : I.Predicates D.sourceFields
  sourceProperties zero value = ⊤
  sourceProperties (suc zero) value = ⊤
  sourceProperties (suc (suc zero)) value = value ≤ sizeMaximum
  sourceProperties (suc (suc (suc zero))) value = value ≤ sizeMaximum
  sourceProperties (suc (suc (suc (suc zero)))) value = ⊤
  sourceProperties (suc (suc (suc (suc (suc ())))))

  sourceDefaults : I.Defaults D.sourceFields sourceProperties
  sourceDefaults (suc (suc (suc (suc (suc ()))))) value observed

  sourceReaders : ∀ allowance index input → S.Ensures (sourceProperties index)
    (Flow.Productive.result (Slots.readerAt D.sourceFields index (R.sourceReaders allowance) input))
  sourceReaders allowance zero input = S.trivial (Flow.Productive.result (R.A.readText input))
  sourceReaders allowance (suc zero) input = S.trivial (Flow.Productive.result (R.A.readText input))
  sourceReaders allowance (suc (suc zero)) input = Inv.uint sizeMaximum input
  sourceReaders allowance (suc (suc (suc zero))) input = Inv.uint sizeMaximum input
  sourceReaders allowance (suc (suc (suc (suc zero)))) input = S.trivial (Flow.Productive.result (R.A.readText input))
  sourceReaders allowance (suc (suc (suc (suc (suc ()))))) input

  sourceBuild : ∀ values → I.Valid D.sourceFields sourceProperties values →
    B.SourceBounds (D.buildSource (Slots.toSequence D.sourceFields values))
  sourceBuild values valid = record { total = valid (suc (suc zero)) ; start = valid (suc (suc (suc zero))) }

  source : ∀ allowance input → S.Ensures B.SourceBounds (Flow.Productive.result (R.source allowance input))
  source allowance input = Inv.recordValue D.sourceFields D.buildSource R.sourceReaders sourceProperties
    B.SourceBounds sourceReaders sourceDefaults sourceBuild allowance input

  deferredProperties : I.Predicates D.deferredFields
  deferredProperties zero value = ⊤
  deferredProperties (suc zero) value = P.I64.InRange value
  deferredProperties (suc (suc ()))

  deferredDefaults : I.Defaults D.deferredFields deferredProperties
  deferredDefaults (suc (suc ())) value observed

  deferredReaders : ∀ allowance index input → S.Ensures (deferredProperties index)
    (Flow.Productive.result (Slots.readerAt D.deferredFields index (R.deferredReaders allowance) input))
  deferredReaders allowance zero input = S.trivial (Flow.Productive.result (R.A.readUUID input))
  deferredReaders allowance (suc zero) input = Inv.signed input
  deferredReaders allowance (suc (suc ())) input

  deferredBuild : ∀ values → I.Valid D.deferredFields deferredProperties values →
    B.DeferredBounds (D.buildDeferred (Slots.toSequence D.deferredFields values))
  deferredBuild values valid = valid (suc zero)

  deferred : ∀ allowance input → S.Ensures B.DeferredBounds (Flow.Productive.result (R.deferred allowance input))
  deferred allowance input = Inv.recordValue D.deferredFields D.buildDeferred R.deferredReaders deferredProperties
    B.DeferredBounds deferredReaders deferredDefaults deferredBuild allowance input

  diagnosticProperties : I.Predicates D.diagnosticFields
  diagnosticProperties zero value = value ≤ P.u64Maximum
  diagnosticProperties (suc zero) value = ⊤
  diagnosticProperties (suc (suc zero)) value = ⊤
  diagnosticProperties (suc (suc (suc zero))) value = ⊤
  diagnosticProperties (suc (suc (suc (suc ()))))

  diagnosticDefaults : I.Defaults D.diagnosticFields diagnosticProperties
  diagnosticDefaults zero value refl = z≤n
  diagnosticDefaults (suc (suc (suc (suc ())))) value observed

  diagnosticReaders : ∀ allowance index input → S.Ensures (diagnosticProperties index)
    (Flow.Productive.result (Slots.readerAt D.diagnosticFields index (R.diagnosticReaders allowance) input))
  diagnosticReaders allowance zero input = Inv.uint P.u64Maximum input
  diagnosticReaders allowance (suc zero) input = S.trivial (Flow.Productive.result (R.A.readUUID input))
  diagnosticReaders allowance (suc (suc zero)) input = S.trivial (Flow.Productive.result (R.A.readText input))
  diagnosticReaders allowance (suc (suc (suc zero))) input = S.trivial (Flow.Productive.result (R.A.readText input))
  diagnosticReaders allowance (suc (suc (suc (suc ())))) input

  diagnosticBuild : ∀ values → I.Valid D.diagnosticFields diagnosticProperties values →
    B.DiagnosticBounds (D.buildDiagnostic (Slots.toSequence D.diagnosticFields values))
  diagnosticBuild values valid = valid zero

  diagnostic : ∀ allowance input → S.Ensures B.DiagnosticBounds (Flow.Productive.result (R.diagnostic allowance input))
  diagnostic allowance input = Inv.recordValue D.diagnosticFields D.buildDiagnostic
    R.diagnosticReaders diagnosticProperties B.DiagnosticBounds
    diagnosticReaders diagnosticDefaults diagnosticBuild allowance
    input

  confirmedProperties : I.Predicates D.confirmedFields
  confirmedProperties zero value = ⊤
  confirmedProperties (suc zero) value = value ≤ P.u64Maximum
  confirmedProperties (suc (suc ()))

  confirmedDefaults : I.Defaults D.confirmedFields confirmedProperties
  confirmedDefaults (suc (suc ())) value observed

  confirmedReaders : ∀ allowance index input → S.Ensures (confirmedProperties index)
    (Flow.Productive.result (Slots.readerAt D.confirmedFields index (R.confirmedReaders allowance) input))
  confirmedReaders allowance zero input = S.trivial (Flow.Productive.result (R.A.readUUID input))
  confirmedReaders allowance (suc zero) input = Inv.uint P.u64Maximum input
  confirmedReaders allowance (suc (suc ())) input

  confirmedBuild : ∀ values → I.Valid D.confirmedFields confirmedProperties values →
    B.ConfirmedBounds (D.buildConfirmed (Slots.toSequence D.confirmedFields values))
  confirmedBuild values valid = valid (suc zero)

  confirmed : ∀ allowance input → S.Ensures B.ConfirmedBounds (Flow.Productive.result (R.confirmed allowance input))
  confirmed allowance input = Inv.recordValue D.confirmedFields D.buildConfirmed
    R.confirmedReaders confirmedProperties B.ConfirmedBounds
    confirmedReaders confirmedDefaults confirmedBuild allowance input
