{-# OPTIONS --safe #-}
-- Canonical UUID lists are accepted by the raw judge UUID-vector reader.
import Mimir.FloatConversion
module Mimir.JudgeUUIDVectorReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Fin using (#_)
open import Data.List using ([]; _∷_; _++_; map)
open import Data.Nat using (ℕ; suc)
open import Relation.Binary.PropositionalEquality using (refl; subst; sym)
import Mimir.UUIDGroups as Groups
import Mimir.UUIDSchema as UUID
import Mimir.JudgeStateSerialize as Serialize
import Mimir.JudgeStateAtoms as AtomsDependency
private
  module Atoms = AtomsDependency floatConversion
import Mimir.JudgeStateRaw as RawDependency
private
  module Raw = RawDependency floatConversion
import Mimir.JudgeUUIDReadBack as ElementDependency
private
  module Element = ElementDependency floatConversion
import Mimir.JsonCompactRecords as Compact
import Mimir.JsonRecordSupport as Support
import Mimir.JsonArrayReadBack as EncodingDependency
private
  module Encoding = EncodingDependency floatConversion
import Mimir.StructuredValue as JSON
import Mimir.SerdeVectorReadBack as VectorDependency
private
  module Vector = VectorDependency floatConversion
import Mimir.SerdeReadBack as Back
import Mimir.SignedMachine as Machine

starts : ∀ value → Vector.Leading (Compact.bytes (UUID.encode value) (Serialize.uuid value))
starts value = Vector.leading (# 34) _ refl (λ ()) (λ ())

module Parser (checks : Machine.OverflowChecks) (sizeMaximum : ℕ) where
  private
    module A = Atoms.Parser checks
    module P = Raw.Parser checks sizeMaximum
    module E = Encoding.Encoding Groups.UUID A.readUUID UUID.encode Serialize.uuid starts
    module V = Vector.Parser checks Groups.UUID (λ allowance → A.readUUID) Raw.arrayExpected

  element : ∀ value suffix → Vector.Delimited suffix →
    Back.Returns A.readUUID
      (Compact.bytes (UUID.encode value) (Serialize.uuid value) ++ suffix) value suffix
  element value suffix delimited = Element.Parser.roundTrip checks value suffix

  roundTrip : ∀ allowance values suffix → Back.Returns (P.uuidVector (suc allowance))
    (Compact.bytes (JSON.array (map UUID.encode values))
      (Compact.array (Support.arrayUniform UUID.encode Serialize.uuid values)) ++ suffix)
    values suffix
  roundTrip allowance values suffix = subst
    (λ input →
       Back.Returns (P.uuidVector (suc allowance)) input values suffix)
    (sym (E.spelling values suffix))
    (V.Encoded.roundTrip allowance
     (λ value →
        Compact.bytes (UUID.encode value) (Serialize.uuid value))
     starts element values suffix)
