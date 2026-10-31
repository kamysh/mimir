{-# OPTIONS --safe #-}
-- Concrete file names, size limits, Unix ancestry and typed record decoders.
-- The receipt retains both the observed file metadata and the exact decoder
-- input. Native adapters still need separate correspondence proofs.
import Mimir.FloatConversion
module Mimir.JudgeRecordRead (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.List using ([]; length)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; _≤_)
open import Data.Sum using (inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Mimir.UnixPath using (Path; join)
import Mimir.UnixPathParent as Parent
import Mimir.JudgePersistence as Names
import Mimir.JudgeParsedRead as Parsed
import Mimir.JudgeStateDocument as DocumentDependency
private
  module Document = DocumentDependency floatConversion
import Mimir.SerdeFlow as Flow
import Mimir.SignedMachine as Machine

module With (Handle NativeError : Set) (checks : Machine.OverflowChecks) (sizeMaximum : ℕ) where
  module D = Document.Parser checks sizeMaximum

  module Named (name : Names.Name) where
    module R = Parsed.With Path Handle NativeError (Document.Value name) (D.read name)

    read : Path → R.FS.Script (R.Outcome (Names.limit name))
    read path = R.readNamed path (join path (Names.filename name)) (Parent.parents path) (Names.limit name)

    consumesDocument : (accepted : R.Loaded (Names.limit name)) →
      Flow.F.Cursor.remaining (R.Loaded.position accepted) ≡ []
    consumesDocument accepted = D.successExhausts name (R.Raw.Read.bytes (R.Loaded.raw accepted))
      (R.Loaded.value accepted) (R.Loaded.position accepted) (R.Loaded.decoded accepted)

    boundedInput : (accepted : R.Loaded (Names.limit name)) →
      length (R.Raw.Read.bytes (R.Loaded.raw accepted)) ≤ Names.limit name
    boundedInput accepted = R.Raw.Read.bounded (R.Loaded.raw accepted)

    readProvenance : ∀ path events accepted →
      R.FS.Runs (read path) events (R.returned (inj₂ (just accepted))) →
      R.FS.Runs (R.Raw.readNamed path (join path (Names.filename name)) (Parent.parents path) (Names.limit name))
        events (inj₂ (just (R.Loaded.raw accepted)))
    readProvenance path events accepted execution = R.successRequiresRawRead path
      (join path (Names.filename name)) (Parent.parents path) (Names.limit name) events accepted execution
