{-# OPTIONS --safe #-}
-- Mimir's three persisted record schemas. The supplied typed JSON library
-- performs syntax decoding; the exact Mimir field/default reader is retained.
import Mimir.StandardLibrary
module Mimir.JudgeStateDocument (library : Mimir.StandardLibrary.Contract) where

open import Data.List using (List)
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_)
open import Mimir.Bits using (Byte)
import Mimir.StandardLibrary as Library
import Mimir.Validation as Validation
import Mimir.StructuredValue as JSON
import Mimir.JudgePersistence as Names
import Mimir.JudgeStateWire as Wire
import Mimir.JudgeStateDecode as Decode
module R = Wire.R

Value : Names.Name → Set
Value Names.status = R.Report
Value Names.failure = R.Incident
Value Names.diagnostics = R.Diagnostics

module Parser (sizeMaximum : ℕ) where
  module D = Decode.Size library sizeMaximum

  recordReader : (name : Names.Name) → JSON.Value → Validation.Fault ⊎ Value name
  recordReader Names.status = D.report
  recordReader Names.failure = D.incident
  recordReader Names.diagnostics = D.diagnostics

  read : (name : Names.Name) → List Byte → Library.ReadResult (recordReader name)
  read name = Library.readRecord library (recordReader name)
