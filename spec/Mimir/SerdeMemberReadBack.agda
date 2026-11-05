{-# OPTIONS --safe #-}
-- Canonical known members parse their key, colon and value into the chosen slot.
import Mimir.FloatConversion
module Mimir.SerdeMemberReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Fin using (#_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (nothing; just)
open import Data.Product using (_,_)
open import Data.Sum using (inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst₂; sym; trans)
import Mimir.SerdeSequence as Sequence
import Mimir.SerdeSlots as Slots
import Mimir.SerdeMember as MemberDependency
private
  module Member = MemberDependency floatConversion
import Mimir.SerdeFlow as Flow
import Mimir.SerdeReadBack as Back
import Mimir.SerdeReadBackComposition as ComposeDependency
private
  module Compose = ComposeDependency floatConversion
import Mimir.JsonString as String
import Mimir.JsonStringParser as Strings
import Mimir.JsonStringWriter as Writer
import Mimir.JsonTextWriter as TextWriter
import Mimir.UnicodeText as Unicode
import Mimir.DecodedText as Decoded

module Record (fields : List Sequence.Field) (readers : Slots.Readers fields) where
  private module M = Member.Record fields readers

  known : ∀ index slots input value suffix →
    Slots.get fields index slots ≡ nothing →
    Back.Returns (Slots.readerAt fields index readers) input value suffix →
    Back.Returned (M.known index slots ((# 58) ∷ input))
      (Slots.put fields index value slots) suffix
  known index slots input value suffix absent receipt rewrite absent = Compose.prefix (Flow.F.cursor (# 58 ∷ []) input refl)
    (Compose.map (λ value → Slots.put fields index value slots)
     receipt)

  afterKey : ∀ name index slots input value suffix →
    Slots.find name fields ≡ just index → Slots.get fields index slots ≡ nothing →
    Back.Returns (Slots.readerAt fields index readers) input value suffix →
    Back.Returned (M.afterKey name slots ((# 58) ∷ input))
      (Slots.put fields index value slots) suffix
  afterKey name index slots input value suffix selected absent receipt rewrite selected = known index slots input value suffix absent receipt

  parsedKey : ∀ slots input (parsed : Strings.Parsed input) →
    Strings.parse input ≡ inj₂ parsed → ∀ output suffix →
    Back.Returned (M.afterKey (Decoded.text (String.values (Strings.Parsed.value parsed)))
      slots (Strings.Parsed.rest parsed)) output suffix →
    Back.Returns (M.member slots) input output suffix
  parsedKey slots input (Strings.parsed value rest exact) selected output suffix receipt
    rewrite selected = Compose.prefix
      (Flow.F.cursor (String.spellString (String.StringValue.body value))
       rest exact)
      receipt

  key : ∀ slots text valid middle output suffix →
    Back.Returned (M.afterKey text slots middle) output suffix →
    Back.Returns (M.member slots)
      (String.spellString (String.StringValue.body (TextWriter.render text valid)) ++ middle)
      output suffix
  key slots text valid middle output suffix receipt
    with Writer.roundTrip (Unicode.encodeValues valid) middle
  ... | result , selected , sameSuffix , sameCodes = parsedKey slots
    (String.spellString
     (String.StringValue.body (TextWriter.render text valid))
     ++ middle)
    result selected output suffix
    (subst₂
     (λ name rest →
        Back.Returned (M.afterKey name slots rest) output suffix)
     (sym
      (trans
       (TextWriter.samePoints
        (String.values (Strings.Parsed.value result))
        (Unicode.encodeValues valid) sameCodes)
       (Decoded.roundTrip valid)))
     (sym sameSuffix) receipt)

  member : ∀ name valid index slots input value suffix →
    Slots.find name fields ≡ just index → Slots.get fields index slots ≡ nothing →
    Back.Returns (Slots.readerAt fields index readers) input value suffix →
    Back.Returns (M.member slots)
      (String.spellString (String.StringValue.body (TextWriter.render name valid)) ++ ((# 58) ∷ input))
      (Slots.put fields index value slots) suffix
  member name valid index slots input value suffix selected absent receipt = key slots name valid (# 58 ∷ input)
    (Slots.put fields index value slots) suffix
    (afterKey name index slots input value suffix selected absent
     receipt)
