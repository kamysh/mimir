{-# OPTIONS --safe #-}
-- Every successfully skipped unknown field leaves all known-field slots unchanged.
import Mimir.FloatConversion
module Mimir.SerdeUnknownMemberReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Fin using (#_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (nothing)
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
import Mimir.JsonString as String
import Mimir.JsonTextWriter as Writer

module Record (fields : List Sequence.Field) (readers : Slots.Readers fields) where
  private
    module M = Member.Record fields readers
    module K = Keys.Record fields readers

  ignored : ∀ slots input suffix →
    Back.Returned (Flow.lift (Ignored.read input)) tt suffix →
    Back.Returned (M.ignored slots ((# 58) ∷ input)) slots suffix
  ignored slots input suffix receipt = Compose.prefix (Flow.F.cursor (# 58 ∷ []) input refl)
    (Compose.map (λ value → slots) receipt)

  afterKey : ∀ name slots input suffix → Slots.find name fields ≡ nothing →
    Back.Returned (Flow.lift (Ignored.read input)) tt suffix →
    Back.Returned (M.afterKey name slots ((# 58) ∷ input)) slots suffix
  afterKey name slots input suffix absent receipt rewrite absent = ignored slots input suffix receipt

  member : ∀ name valid slots input suffix → Slots.find name fields ≡ nothing →
    Back.Returned (Flow.lift (Ignored.read input)) tt suffix →
    Back.Returns (M.member slots)
      (String.spellString (String.StringValue.body (Writer.render name valid)) ++ ((# 58) ∷ input))
      slots suffix
  member name valid slots input suffix absent receipt = K.key slots name valid (# 58 ∷ input) slots suffix
    (afterKey name slots input suffix absent receipt)
