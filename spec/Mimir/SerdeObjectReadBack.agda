{-# OPTIONS --safe #-}
-- Constructive read-back of complete canonical objects from typed member evidence.
import Mimir.FloatConversion
module Mimir.SerdeObjectReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; #_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (nothing; just)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
import Mimir.SerdeRecord as TypedRecordDependency
private
  module TypedRecord = TypedRecordDependency floatConversion
import Mimir.SignedMachine as Machine
import Mimir.Validation as V
import Mimir.StructuredValue as JSON
import Mimir.SerdeSequence as Sequence
import Mimir.SerdeSlots as Slots
import Mimir.SerdeMap as MapDependency
private
  module Map = MapDependency floatConversion
import Mimir.SerdeMapReadBack as MapBackDependency
private
  module MapBack = MapBackDependency floatConversion
import Mimir.SerdeMemberReadBack as MemberBackDependency
private
  module MemberBack = MemberBackDependency floatConversion
import Mimir.SerdeUnknownMemberReadBack as UnknownBackDependency
private
  module UnknownBack = UnknownBackDependency floatConversion
import Mimir.SerdeFlow as Flow
import Mimir.JsonIgnoredRun as IgnoredDependency
private
  module Ignored = IgnoredDependency floatConversion
import Mimir.SerdeReadBack as Back
import Mimir.JsonCompactRecords as Compact
import Mimir.JsonObjectReadBack as Encoding

module Record (fields : List Sequence.Field) (readers : Slots.Readers fields) where
  private
    module M = Map.Record fields readers
    module P = MapBack.Record fields readers
    module Member = MemberBack.Record fields readers
    module Unknown = UnknownBack.Record fields readers

  data Written : (first : Bool) → Slots.Slots fields →
      ∀ pairs → All Compact.FieldSupported pairs → Slots.Slots fields → Set where
    done : ∀ first slots → Written first slots [] All.[] slots
    emitted : ∀ {first slots name encoded nameValid valid pairs rest final}
      (index : Fin (length fields)) (value : Sequence.Field.Carrier (Slots.fieldAt fields index)) →
      Slots.find name fields ≡ just index → Slots.get fields index slots ≡ nothing →
      (∀ suffix → Encoding.Delimited suffix →
        Back.Returns (Slots.readerAt fields index readers)
          (Compact.bytes encoded valid ++ suffix) value suffix) →
      Written false (Slots.put fields index value slots) pairs rest final →
      Written first slots ((name , encoded) ∷ pairs) ((nameValid , valid) All.∷ rest) final
    skipped : ∀ {first slots name encoded nameValid valid pairs rest final} →
      Slots.find name fields ≡ nothing →
      (∀ suffix → Encoding.Delimited suffix →
        Back.Returned (Flow.lift (Ignored.read (Compact.bytes encoded valid ++ suffix))) tt suffix) →
      Written false slots pairs rest final →
      Written first slots ((name , encoded) ∷ pairs) ((nameValid , valid) All.∷ rest) final

  roundTrip : ∀ {first slots pairs valid final} → Written first slots pairs valid final → ∀ suffix →
    Back.Returned (M.Machine.read (first , slots) (Encoding.members first pairs valid suffix))
      final ((# 125) ∷ suffix)
  roundTrip (done first slots) suffix = P.closed first slots suffix
  roundTrip (emitted {first = true} {slots = slots} {name = name} {encoded = encoded} {nameValid = nameValid} {valid = valid} {pairs = pairs} {rest = rest} {final = final}
    index value selected absent readValue tail) suffix = P.next true slots
      (Encoding.member (name , encoded) (nameValid , valid)
       (Encoding.members false pairs rest suffix))
      []
      (Encoding.member (name , encoded) (nameValid , valid)
       (Encoding.members false pairs rest suffix))
      refl (Slots.put fields index value slots)
      (Encoding.members false pairs rest suffix) final (# 125 ∷ suffix)
      (MapBack.firstControl _)
      (Member.member name nameValid index slots
       (Compact.bytes encoded valid ++
        Encoding.members false pairs rest suffix)
       value (Encoding.members false pairs rest suffix) selected absent
       (readValue (Encoding.members false pairs rest suffix)
        (Encoding.delimited pairs rest suffix)))
      (roundTrip tail suffix)
  roundTrip (emitted {first = false} {slots = slots} {name = name} {encoded = encoded} {nameValid = nameValid} {valid = valid} {pairs = pairs} {rest = rest} {final = final}
    index value selected absent readValue tail) suffix = P.next false slots
      (# 44 ∷
       Encoding.member (name , encoded) (nameValid , valid)
       (Encoding.members false pairs rest suffix))
      (# 44 ∷ [])
      (Encoding.member (name , encoded) (nameValid , valid)
       (Encoding.members false pairs rest suffix))
      refl (Slots.put fields index value slots)
      (Encoding.members false pairs rest suffix) final (# 125 ∷ suffix)
      (MapBack.laterControl _)
      (Member.member name nameValid index slots
       (Compact.bytes encoded valid ++
        Encoding.members false pairs rest suffix)
       value (Encoding.members false pairs rest suffix) selected absent
       (readValue (Encoding.members false pairs rest suffix)
        (Encoding.delimited pairs rest suffix)))
      (roundTrip tail suffix)

  roundTrip (skipped {first = true} {slots = slots} {name = name} {encoded = encoded} {nameValid = nameValid} {valid = valid} {pairs = pairs} {rest = rest} {final = final}
    absent skip tail) suffix = P.next true slots
      (Encoding.member (name , encoded) (nameValid , valid)
       (Encoding.members false pairs rest suffix))
      []
      (Encoding.member (name , encoded) (nameValid , valid)
       (Encoding.members false pairs rest suffix))
      refl slots (Encoding.members false pairs rest suffix) final
      (# 125 ∷ suffix) (MapBack.firstControl _)
      (Unknown.member name nameValid slots
       (Compact.bytes encoded valid ++
        Encoding.members false pairs rest suffix)
       (Encoding.members false pairs rest suffix) absent
       (skip (Encoding.members false pairs rest suffix)
        (Encoding.delimited pairs rest suffix)))
      (roundTrip tail suffix)
  roundTrip (skipped {first = false} {slots = slots} {name = name} {encoded = encoded} {nameValid = nameValid} {valid = valid} {pairs = pairs} {rest = rest} {final = final}
    absent skip tail) suffix = P.next false slots
      (# 44 ∷
       Encoding.member (name , encoded) (nameValid , valid)
       (Encoding.members false pairs rest suffix))
      (# 44 ∷ [])
      (Encoding.member (name , encoded) (nameValid , valid)
       (Encoding.members false pairs rest suffix))
      refl slots (Encoding.members false pairs rest suffix) final
      (# 125 ∷ suffix) (MapBack.laterControl _)
      (Unknown.member name nameValid slots
       (Compact.bytes encoded valid ++
        Encoding.members false pairs rest suffix)
       (Encoding.members false pairs rest suffix) absent
       (skip (Encoding.members false pairs rest suffix)
        (Encoding.delimited pairs rest suffix)))
      (roundTrip tail suffix)

module Parser (checks : Machine.OverflowChecks) (fields : List Sequence.Field)
  (readers : ℕ → Slots.Readers fields) (expected : V.Fault) where
  private module P = TypedRecord.Parser checks fields readers expected

  roundTrip : ∀ allowance pairs valid slots values suffix →
    Record.Written fields (readers allowance) true (Slots.empty fields) pairs valid slots →
    Slots.Resolved fields slots values →
    Back.Returns (P.read (suc allowance))
      (Compact.bytes (JSON.object pairs) (Compact.object valid) ++ suffix) values suffix
  roundTrip allowance pairs valid slots values suffix written resolved = subst
    (λ input →
       Back.Returns (P.read (suc allowance)) input values suffix)
    (sym (Encoding.spelling pairs valid suffix))
    (MapBack.Parser.closeContainer checks fields readers expected
     allowance (Encoding.members true pairs valid suffix) values suffix
     (MapBack.Record.body fields (readers allowance)
      (Encoding.members true pairs valid suffix) slots values
      (# 125 ∷ suffix)
      (Record.roundTrip fields (readers allowance) written suffix)
      resolved))
