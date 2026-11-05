{-# OPTIONS --safe #-}
-- Known values and arbitrary nested ignored values compose through the actual
-- typed member reader, including whitespace before and after the colon.
import Mimir.FloatConversion
module Mimir.SerdeSpacedMemberReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Fin using (#_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (nothing; just)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.SerdeSequence as Sequence
import Mimir.SerdeSlots as Slots
import Mimir.SerdeMember as MemberDependency
private
  module Member = MemberDependency floatConversion
import Mimir.SerdeMemberReadBack as KeysDependency
private
  module Keys = KeysDependency floatConversion
import Mimir.SerdeFlow as Flow
import Mimir.SerdeReadBack as Back
import Mimir.SerdeReadBackComposition as ComposeDependency
private
  module Compose = ComposeDependency floatConversion
import Mimir.JsonIgnoredRun as IgnoredDependency
private
  module Ignored = IgnoredDependency floatConversion
import Mimir.JsonIgnoredKeyWhitespace as ColonDependency
private
  module Colon = ColonDependency floatConversion
import Mimir.JsonIgnoredSpacedSyntax as SyntaxDependency
private
  module Syntax = SyntaxDependency floatConversion
import Mimir.JsonIgnoredSpacedReadBack as ReadBackDependency
private
  module ReadBack = ReadBackDependency floatConversion
import Mimir.JsonIgnoredNumberReadBack as Character
import Mimir.JsonControls as Controls
import Mimir.ByteText as Wire
import Mimir.JsonString as String
import Mimir.JsonTextWriter as Writer

module Record (fields : List Sequence.Field) (readers : Slots.Readers fields) where
  private
    module M = Member.Record fields readers
    module K = Keys.Record fields readers

  known : ∀ index slots before input value suffix →
    Slots.get fields index slots ≡ nothing →
    Back.Returns (Slots.readerAt fields index readers) input value suffix →
    Back.Returned (M.known index slots (Syntax.Gap.bytes before ++ ((# 58) ∷ input)))
      (Slots.put fields index value slots) suffix
  known index slots before input value suffix absent receipt rewrite absent = Compose.andThen
    (Flow.lift
     (Controls.colon (Syntax.Gap.bytes before ++ # 58 ∷ input)))
    (λ First Second →
       Flow.map (λ input₁ → Slots.put fields index input₁ slots)
       (Flow.Productive.result
        (Slots.readerAt fields index readers Second)))
    (Colon.colon (Syntax.Gap.bytes before) (Syntax.Gap.valid before)
     input)
    (Compose.mapProductive
     (λ result → Slots.put fields index result slots)
     (Slots.readerAt fields index readers input) receipt)

  afterKnown : ∀ name index slots before input value suffix →
    Slots.find name fields ≡ just index → Slots.get fields index slots ≡ nothing →
    Back.Returns (Slots.readerAt fields index readers) input value suffix →
    Back.Returned (M.afterKey name slots (Syntax.Gap.bytes before ++ ((# 58) ∷ input)))
      (Slots.put fields index value slots) suffix
  afterKnown name index slots before input value suffix selected absent receipt rewrite selected = known index slots before input value suffix absent receipt

  knownMember : ∀ name valid index slots before input value suffix →
    Slots.find name fields ≡ just index → Slots.get fields index slots ≡ nothing →
    Back.Returns (Slots.readerAt fields index readers) input value suffix →
    Back.Returns (M.member slots)
      (String.spellString (String.StringValue.body (Writer.render name valid)) ++
       (Syntax.Gap.bytes before ++ ((# 58) ∷ input))) (Slots.put fields index value slots) suffix
  knownMember name valid index slots before input value suffix selected absent receipt = K.key slots name valid (Syntax.Gap.bytes before ++ # 58 ∷ input)
    (Slots.put fields index value slots) suffix
    (afterKnown name index slots before input value suffix selected
     absent receipt)

  ignored : ∀ slots before item suffix → Character.Stopped (Wire.text suffix) →
    Back.Returned (M.ignored slots
      (Syntax.Gap.bytes before ++ ((# 58) ∷ Syntax.spell item suffix))) slots suffix
  ignored slots before item suffix stopped = Compose.andThen
    (Flow.lift
     (Controls.colon
      (Syntax.Gap.bytes before ++ # 58 ∷ Syntax.spell item suffix)))
    (λ unit rest →
       Flow.map (λ value → slots) (Flow.lift (Ignored.read rest)))
    (Colon.colon (Syntax.Gap.bytes before) (Syntax.Gap.valid before)
     (Syntax.spell item suffix))
    (Compose.map (λ value → slots)
     (ReadBack.complete item suffix stopped))

  afterUnknown : ∀ name slots before item suffix → Slots.find name fields ≡ nothing →
    Character.Stopped (Wire.text suffix) →
    Back.Returned (M.afterKey name slots
      (Syntax.Gap.bytes before ++ ((# 58) ∷ Syntax.spell item suffix))) slots suffix
  afterUnknown name slots before item suffix absent stopped rewrite absent = ignored slots before item suffix stopped

  unknownMember : ∀ name valid slots before item suffix → Slots.find name fields ≡ nothing →
    Character.Stopped (Wire.text suffix) →
    Back.Returns (M.member slots)
      (String.spellString (String.StringValue.body (Writer.render name valid)) ++
       (Syntax.Gap.bytes before ++ ((# 58) ∷ Syntax.spell item suffix))) slots suffix
  unknownMember name valid slots before item suffix absent stopped = K.key slots name valid
    (Syntax.Gap.bytes before ++ # 58 ∷ Syntax.spell item suffix) slots
    suffix (afterUnknown name slots before item suffix absent stopped)
