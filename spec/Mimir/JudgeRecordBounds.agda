{-# OPTIONS --safe #-}
-- Transfer complete-document bounds to the original guarded read receipt.
import Mimir.FloatConversion
module Mimir.JudgeRecordBounds (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Nat using (ℕ)
import Mimir.JudgePersistence as Names
import Mimir.JudgeDocumentBounds as DocumentBoundsDependency
private
  module DocumentBounds = DocumentBoundsDependency floatConversion
import Mimir.JudgeRecordRead as RecordReadDependency
private
  module RecordRead = RecordReadDependency floatConversion
import Mimir.SignedMachine as Machine

module With (Handle NativeError : Set) (checks : Machine.OverflowChecks) (sizeMaximum : ℕ) where
  loaded : ∀ name (accepted : RecordRead.With.Named.R.Loaded Handle NativeError checks sizeMaximum name (Names.limit name)) →
    DocumentBounds.Size.Valid sizeMaximum name
      (RecordRead.With.Named.R.Loaded.value accepted)
  loaded name accepted = DocumentBounds.Parser.successful checks sizeMaximum name
    (RecordRead.With.Named.R.Raw.Read.bytes {checks = checks} {sizeMaximum = sizeMaximum} {name = name}
     (RecordRead.With.Named.R.Loaded.raw accepted))
    (RecordRead.With.Named.R.Loaded.value accepted)
    (RecordRead.With.Named.R.Loaded.position accepted)
    (RecordRead.With.Named.R.Loaded.decoded accepted)
