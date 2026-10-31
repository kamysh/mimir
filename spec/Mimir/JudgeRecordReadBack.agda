{-# OPTIONS --safe #-}
-- Guarded reads of the concrete writer bytes restore the original typed record.
import Mimir.FloatConversion
module Mimir.JudgeRecordReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; _≤_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)
open import Mimir.UnixPath using (Path; join)
import Mimir.UnixPathParent as Parent
import Mimir.JudgePersistence as Names
import Mimir.JudgeRecordWrite as Write
import Mimir.JudgeRecordRead as ReadDependency
private
  module Read = ReadDependency floatConversion
import Mimir.JudgeStateDocument as DocumentDependency
private
  module Document = DocumentDependency floatConversion
import Mimir.JudgeStateDocumentReadBack as CodecDependency
private
  module Codec = CodecDependency floatConversion
import Mimir.JudgeParsedReadBack as Parsed
import Mimir.JudgeStatePrimitives as Primitive
import Mimir.SerdeReadBack as Back
import Mimir.SignedMachine as Machine

module With (Handle NativeError : Set) (checks : Machine.OverflowChecks) (sizeMaximum : ℕ)
  (nativeWidth : sizeMaximum ≤ Primitive.u64Maximum) where
  private
    module W = Write.Size sizeMaximum
    module D = Document.Parser checks sizeMaximum
    module C = Codec.Parser checks sizeMaximum nativeWidth
    module Reader = Read.With Handle NativeError checks sizeMaximum

  value : ∀ {name} → W.Value name → Document.Value name
  value (W.report item bounded valid) = item
  value (W.incident item bounded valid) = item
  value (W.diagnostics records bounded valid) = records

  codec : ∀ {name} (item : W.Value name) →
    Back.Returns (D.read name) (W.bytes item) (value item) []
  codec (W.report item bounded valid) = C.roundTrip Names.status item valid bounded
  codec (W.incident item bounded valid) = C.roundTrip Names.failure item valid bounded
  codec (W.diagnostics records bounded valid) = C.roundTrip Names.diagnostics records valid bounded

  module Named (name : Names.Name) where
    private
      module N = Reader.Named name
      module P = N.R
      module Proof = Parsed.With Path Handle NativeError (Document.Value name) (D.read name)

    canonical : (raw : P.Raw.Read (Names.limit name)) (item : W.Value name) →
      P.Raw.Read.bytes raw ≡ W.bytes item →
      Back.Returns (D.read name) (P.Raw.Read.bytes raw) (value item) []
    canonical raw item same = subst (λ input → Back.Returns (D.read name) input (value item) [])
      (sym same) (codec item)

    read : ∀ path events (raw : P.Raw.Read (Names.limit name)) (item : W.Value name) →
      P.FS.Runs (P.Raw.readNamed path (join path (Names.filename name)) (Parent.parents path) (Names.limit name))
        events (inj₂ (just raw)) → P.Raw.Read.bytes raw ≡ W.bytes item →
      Σ (P.Loaded (Names.limit name)) (λ accepted →
        P.FS.Runs (N.read path) events (P.returned (inj₂ (just accepted))) ×
        P.Loaded.value accepted ≡ value item × P.Loaded.raw accepted ≡ raw)
    read path events raw item execution same = Proof.read path (join path (Names.filename name))
      (Parent.parents path) (Names.limit name) events raw (value item)
      execution (canonical raw item same)
