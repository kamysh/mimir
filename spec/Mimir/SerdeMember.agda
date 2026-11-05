{-# OPTIONS --safe #-}
-- Raw struct members retain known-field presence and skip unknown values with
-- the serde ignored-value grammar. A duplicate is rejected before reading its
-- colon or value, as in the generated Deserialize visitor.
import Mimir.FloatConversion
module Mimir.SerdeMember (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.List using (List; length)
open import Data.Fin using (Fin)
open import Data.Maybe using (nothing; just)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.SerdeSequence as Sequence
import Mimir.SerdeSlots as Slots
import Mimir.SerdeFlow as Flow
import Mimir.JsonAtoms as AtomsDependency
private
  module Atoms = AtomsDependency floatConversion
import Mimir.JsonString as String
import Mimir.DecodedText as Decoded
import Mimir.JsonControls as Controls
import Mimir.JsonIgnoredRun as IgnoredDependency
private
  module Ignored = IgnoredDependency floatConversion

module Record (fields : List Sequence.Field) (readers : Slots.Readers fields) where
  known : Fin (length fields) → Slots.Slots fields → ∀ input → Flow.Result (Slots.Slots fields) input
  known index slots input with Slots.get fields index slots
  ... | just previous = Flow.reject (Slots.duplicate (Slots.fieldAt fields index)) input
  ... | nothing = Flow.andThen (Flow.lift (Controls.colon input)) λ unit rest →
    Flow.map (λ value → Slots.put fields index value slots)
      (Flow.Productive.result (Slots.readerAt fields index readers rest))

  ignored : Slots.Slots fields → ∀ input → Flow.Result (Slots.Slots fields) input
  ignored slots input = Flow.andThen (Flow.lift (Controls.colon input)) λ unit rest →
    Flow.map (λ value → slots) (Flow.lift (Ignored.read rest))

  afterKey : Text → Slots.Slots fields → ∀ input → Flow.Result (Slots.Slots fields) input
  afterKey name slots input with Slots.find name fields
  ... | just index = known index slots input
  ... | nothing = ignored slots input

  member : Slots.Slots fields → Flow.Parser (Slots.Slots fields)
  member slots input = Flow.bindProductive (Flow.fromJsonProductive (Atoms.string input)) λ key rest →
    afterKey (Decoded.text (String.values key)) slots rest

  duplicateBeforeValue : ∀ index slots previous input → Slots.get fields index slots ≡ just previous →
    known index slots input ≡ Flow.reject (Slots.duplicate (Slots.fieldAt fields index)) input
  duplicateBeforeValue index slots previous input present rewrite present = refl

  unknownSelectsIgnored : ∀ name slots input → Slots.find name fields ≡ nothing →
    afterKey name slots input ≡ ignored slots input
  unknownSelectsIgnored name slots input absent rewrite absent = refl

  knownSelectsReader : ∀ name index slots input → Slots.find name fields ≡ just index →
    afterKey name slots input ≡ known index slots input
  knownSelectsReader name index slots input selected rewrite selected = refl
