{-# OPTIONS --safe #-}
-- Concrete record codecs and named filesystem protocols behind judge storage.
-- Application IDs are projections of native UUID records, not arbitrary
-- encoder callbacks. A normal receipt excludes a parser/randomness panic;
-- interrupted prefixes remain possible without a fabricated acknowledgement.
module Mimir.JudgePersistenceComposition where

open import Data.List using (List; map; length)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤?_)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.String using (toList)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Mimir.Text using (Text)
open import Mimir.Bits using (Byte)
import Mimir.JudgePersistence as Names
import Mimir.JudgeStateRecords as Records
import Mimir.JudgeStateMap as Mapping
import Mimir.JudgeStateDocument as Document
import Mimir.JudgeRecordWrite as Write
import Mimir.JudgeFilesystem as Filesystem
import Mimir.FloatConversion as Conversion
import Mimir.SerdeFlow as Flow
import Mimir.SignedMachine as Machine
import Mimir.UnixPath as Path
import Mimir.UUIDV4 as UUID

module R = Records.Over ℕ
module Map = Mapping.Native

Logical : Names.Name → Set
Logical Names.status = R.Report
Logical Names.failure = R.Incident
Logical Names.diagnostics = R.Diagnostics

module Storage (conversion : Conversion.Contract) (sizeMaximum : ℕ) (endian : UUID.Endian) where
  module D = Document conversion
  module Parser = D.Parser Machine.disabled sizeMaximum
  module File = Names.With ℕ Text
  module FS = Filesystem.With Path.Path ℕ Text
  module W = Write.Size sizeMaximum
  module Writer = W.With ℕ Text Text

  convert : (name : Names.Name) → D.Value name → Logical name
  convert Names.status = Map.report
  convert Names.failure = Map.incident
  convert Names.diagnostics = map Map.trace

  data DecodeError : Set where invalid panicked : DecodeError

  decoded : ∀ {A input} → Flow.Result A input → DecodeError ⊎ A
  decoded (Flow.ordinary (Flow.F.success value cursor)) = inj₂ value
  decoded (Flow.ordinary (Flow.F.failure failure)) = inj₁ invalid
  decoded (Flow.panicked cursor) = inj₁ panicked

  decode : (name : Names.Name) → List Byte → DecodeError ⊎ D.Value name
  decode name bytes = decoded (Flow.Productive.result (Parser.read name bytes))

  OrdinaryDecode : Names.Name → List Byte → Set
  OrdinaryDecode name bytes with Flow.Productive.result (Parser.read name bytes)
  ... | Flow.ordinary result = ⊤
  ... | Flow.panicked cursor = ⊥

  Clean : Names.Name → FS.Event → Set
  Clean name (FS.readAtMost handle limit , inj₂ bytes) with length bytes ≤? Names.limit name
  ... | yes bounded = OrdinaryDecode name bytes
  ... | no oversized = ⊤
  Clean name event = ⊤

  module Reading (name : Names.Name) where
    module Reader = File.Decoder (D.Value name) DecodeError (decode name)
    Result = FS.Result (Maybe (Reader.R.Read (Names.limit name)))

    project : Result → Text ⊎ Maybe (Logical name)
    project (inj₁ error) = inj₁ (toList "judge state unavailable")
    project (inj₂ nothing) = inj₂ nothing
    project (inj₂ (just value)) = inj₂ (just (convert name (Reader.R.Read.value value)))

    record Receipt (path : Path.Path) (reply : Text ⊎ Maybe (Logical name)) : Set where
      field events : List FS.Event
            result : Result
            execution : FS.Runs (Reader.read path name) events result
            normal : All (Clean name) events
            exact : project result ≡ reply

  nativeValue : ∀ {name} → W.Value name → D.Value name
  nativeValue (W.report value bounded valid) = value
  nativeValue (W.incident value bounded valid) = value
  nativeValue (W.diagnostics value bounded valid) = value

  data Acknowledges : Writer.W.Outcome → Text ⊎ ⊤ → Set where
    succeeded : Acknowledges (Writer.W.returned (inj₂ tt)) (inj₂ tt)
    failed : ∀ cause → Acknowledges (Writer.W.returned (inj₁ cause)) (inj₁ (toList "judge state write failed"))

  record Written (path : Path.Path) (name : Names.Name) (logical : Logical name) (reply : Text ⊎ ⊤) : Set where
    field value : W.Value name
          represented : convert name (nativeValue value) ≡ logical
          events : List Writer.W.P.Event
          result : Writer.W.Outcome
          execution : Writer.W.P.Runs (Writer.write path endian value) events result
          acknowledged : Acknowledges result reply
