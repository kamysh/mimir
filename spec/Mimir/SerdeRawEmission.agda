{-# OPTIONS --safe #-}
-- Schema-ordered raw emission mirrors SerdeEmission and retains omitted defaults.
import Mimir.FloatConversion
module Mimir.SerdeRawEmission (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Bool using (true; false)
open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
import Data.Nat as Nat
open import Data.Product using (_,_; proj₁)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.SignedMachine as Machine
import Mimir.Validation as V
import Mimir.StructuredValue as JSON
import Mimir.SerdeRecord as TypedRecordDependency
private
  module TypedRecord = TypedRecordDependency floatConversion
import Mimir.SerdeSequence as Sequence
import Mimir.SerdeStruct as Struct
import Mimir.SerdeSlots as Slots
import Mimir.SerdeFlow as Flow
import Mimir.SerdeReadBack as Back
import Mimir.SerdeObjectReadBack as ObjectDependency
private
  module Object = ObjectDependency floatConversion
import Mimir.JsonObjects as Objects
import Mimir.JsonCompactRecords as Compact
import Mimir.JsonObjectReadBack as Encoding
module N = Objects.Names
open Sequence using (Field)

data Emits : (fields : List Field) → Slots.Readers fields → Slots.Values fields →
    ∀ pairs → All Compact.FieldSupported pairs → Set₁ where
  done : Emits [] tt tt [] All.[]
  emitted : ∀ {entry rest reader readers value values raw input rawValid nameValid inputValid} →
    (∀ suffix → Encoding.Delimited suffix →
      Back.Returns reader (Compact.bytes raw rawValid ++ suffix) value suffix) →
    Emits rest readers values input inputValid →
    Emits (entry ∷ rest) (reader , readers) (value , values)
      ((Field.name entry , raw) ∷ input) ((nameValid , rawValid) All.∷ inputValid)
  omitted : ∀ {entry rest reader readers value values input inputValid} →
    Field.missing entry ≡ just value → Emits rest readers values input inputValid →
    Emits (entry ∷ rest) (reader , readers) (value , values) input inputValid

stored : ∀ {fields readers values pairs valid} → Emits fields readers values pairs valid → Slots.Slots fields
stored done = tt
stored (emitted {value = value} read tail) = just value , stored tail
stored (omitted fallback tail) = nothing , stored tail

resolved : ∀ {fields readers values pairs valid} (receipt : Emits fields readers values pairs valid) →
  Slots.Resolved fields (stored receipt) values
resolved done = Slots.resolvedEmpty
resolved (emitted read tail) = Slots.supplied (resolved tail)
resolved (omitted fallback tail) = Slots.defaulted fallback (resolved tail)

absentEmitted : ∀ {fields readers values pairs valid} name → N.Absent name (Struct.names fields) →
  Emits fields readers values pairs valid → N.Absent name (map proj₁ pairs)
absentEmitted name All.[] done = All.[]
absentEmitted name (different All.∷ others) (emitted read tail) = different All.∷ absentEmitted name others tail
absentEmitted name (different All.∷ others) (omitted fallback tail) = absentEmitted name others tail

findHead : ∀ entry fields → Slots.find (Field.name entry) (entry ∷ fields) ≡ just zero
findHead entry fields with Field.name entry ≟Text Field.name entry
... | yes same = refl
... | no different = ⊥-elim (different refl)

findAfter : ∀ entry fields name index → Field.name entry ≢ name →
  Slots.find name fields ≡ just index → Slots.find name (entry ∷ fields) ≡ just (suc index)
findAfter entry fields name index different selected with name ≟Text Field.name entry
... | yes same = ⊥-elim (different (sym same))
... | no other rewrite selected = refl

findAbsentAfter : ∀ entry fields name → Field.name entry ≢ name →
  Slots.find name fields ≡ nothing → Slots.find name (entry ∷ fields) ≡ nothing
findAbsentAfter entry fields name different absent with name ≟Text Field.name entry
... | yes same = ⊥-elim (different (sym same))
... | no other rewrite absent = refl

weaken : ∀ {fields readers first slots pairs valid final} (entry : Field)
  (reader : Flow.Parser (Field.Carrier entry)) (head : Maybe (Field.Carrier entry)) →
  N.Absent (Field.name entry) (map proj₁ pairs) →
  Object.Record.Written fields readers first slots pairs valid final →
  Object.Record.Written (entry ∷ fields) (reader , readers) first (head , slots) pairs valid (head , final)
weaken entry reader head absent (Object.Record.done first slots) = Object.Record.done first (head , slots)
weaken {fields = fields} entry reader head (different All.∷ others)
  (Object.Record.emitted {name = name} index value selected fresh read tail) = Object.Record.emitted (suc index) value
    (findAfter entry fields name index different selected) fresh read
    (weaken entry reader head others tail)
weaken {fields = fields} entry reader head (different All.∷ others)
  (Object.Record.skipped {name = name} absent skip tail) = Object.Record.skipped
    (findAbsentAfter entry fields name different absent) skip
    (weaken entry reader head others tail)

written : ∀ {fields readers values pairs valid} → N.Unique (Struct.names fields) →
  (receipt : Emits fields readers values pairs valid) → ∀ first →
  Object.Record.Written fields readers first (Slots.empty fields) pairs valid (stored receipt)
written unique done first = Object.Record.done first tt
written (absent , unique)
  (emitted {entry = entry} {rest = rest} {reader = reader} {value = value} read tail) first = Object.Record.emitted zero value (findHead entry rest) refl read
    (weaken entry reader (just value)
     (absentEmitted (Field.name entry) absent tail)
     (written unique tail false))
written (absent , unique)
  (omitted {entry = entry} {reader = reader} fallback tail) first = weaken entry reader nothing
    (absentEmitted (Field.name entry) absent tail)
    (written unique tail first)

module Parser (checks : Machine.OverflowChecks) (fields : List Field)
  (readers : ℕ → Slots.Readers fields) (expected : V.Fault) where
  private module P = TypedRecord.Parser checks fields readers expected

  roundTrip : ∀ allowance values pairs valid → N.Unique (Struct.names fields) →
    Emits fields (readers allowance) values pairs valid → ∀ suffix →
    Back.Returns (P.read (Nat.suc allowance))
      (Compact.bytes (JSON.object pairs) (Compact.object valid) ++ suffix) values suffix
  roundTrip allowance values pairs valid unique receipt suffix = Object.Parser.roundTrip checks fields readers expected allowance
    pairs valid (stored receipt) values suffix
    (written unique receipt true) (resolved receipt)
