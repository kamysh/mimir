{-# OPTIONS --safe #-}
-- Known and unknown members preserve the original parse diagnostic. Duplicate
-- known fields are refused before any colon/value parser can contribute one.
import Mimir.FloatConversion
module Mimir.SerdeMemberFailure (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.List using (List)
open import Data.Maybe using (nothing; just)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.SerdeSequence as Sequence
import Mimir.SerdeSlots as Slots
import Mimir.SerdeMember as MemberDependency
private
  module Member = MemberDependency floatConversion
import Mimir.SerdeFlow as Flow
import Mimir.SerdeReadBack as Back
import Mimir.SerdeFailure as Failure
import Mimir.JsonIgnoredFailure as IgnoredFailureDependency
private
  module IgnoredFailure = IgnoredFailureDependency floatConversion
import Mimir.JsonIgnoredRun as IgnoredDependency
private
  module Ignored = IgnoredDependency floatConversion
import Mimir.JsonControls as Controls
import Mimir.JsonAtoms as AtomsDependency
private
  module Atoms = AtomsDependency floatConversion
import Mimir.JsonString as String
import Mimir.DecodedText as Decoded

ignoredFailure : ∀ input code suffix → IgnoredFailure.Failed (Ignored.read input) code suffix →
  Failure.Rejected (Flow.lift (Ignored.read input)) (Flow.syntaxFault code) suffix
ignoredFailure input code suffix receipt with Ignored.read input
... | Controls.C.failure actual consumed remaining exact with receipt
...   | IgnoredFailure.failed = Failure.fromSyntax input actual consumed remaining exact
ignoredFailure input code suffix () | Controls.C.success value consumed remaining exact

module Record (fields : List Sequence.Field) (readers : Slots.Readers fields) where
  private module M = Member.Record fields readers

  duplicate : ∀ index slots previous input → Slots.get fields index slots ≡ just previous →
    Failure.Rejected (M.known index slots input)
      (Flow.visitor (Slots.duplicate (Slots.fieldAt fields index))) input
  duplicate index slots previous input present rewrite present = Failure.rejected (Flow.F.initial input) refl refl

  knownColon : ∀ index slots input code suffix → Slots.get fields index slots ≡ nothing →
    Failure.Rejected (Flow.lift (Controls.colon input)) code suffix →
    Failure.Rejected (M.known index slots input) code suffix
  knownColon index slots input code suffix absent receipt rewrite absent = Failure.andThen (Flow.lift (Controls.colon input))
    (λ unit rest →
       Flow.map (λ value → Slots.put fields index value slots)
       (Flow.Productive.result
        (Slots.readerAt fields index readers rest)))
    receipt

  knownValue : ∀ index slots input middle code suffix → Slots.get fields index slots ≡ nothing →
    Back.Returned (Flow.lift (Controls.colon input)) tt middle →
    Failure.Rejected (Flow.Productive.result (Slots.readerAt fields index readers middle)) code suffix →
    Failure.Rejected (M.known index slots input) code suffix
  knownValue index slots input middle code suffix absent colon receipt rewrite absent = Failure.afterSuccess (Flow.lift (Controls.colon input))
    (λ unit rest →
       Flow.map (λ value → Slots.put fields index value slots)
       (Flow.Productive.result
        (Slots.readerAt fields index readers rest)))
    colon
    (Failure.mapProductive
     (λ value → Slots.put fields index value slots)
     (Slots.readerAt fields index readers middle) receipt)

  ignoredColon : ∀ slots input code suffix →
    Failure.Rejected (Flow.lift (Controls.colon input)) code suffix →
    Failure.Rejected (M.ignored slots input) code suffix
  ignoredColon slots input code suffix receipt = Failure.andThen (Flow.lift (Controls.colon input))
    (λ unit rest →
       Flow.map (λ value → slots) (Flow.lift (Ignored.read rest)))
    receipt

  ignoredValue : ∀ slots input middle code suffix →
    Back.Returned (Flow.lift (Controls.colon input)) tt middle →
    IgnoredFailure.Failed (Ignored.read middle) code suffix →
    Failure.Rejected (M.ignored slots input) (Flow.syntaxFault code) suffix
  ignoredValue slots input middle code suffix colon receipt = Failure.afterSuccess (Flow.lift (Controls.colon input))
    (λ unit rest →
       Flow.map (λ value → slots) (Flow.lift (Ignored.read rest)))
    colon
    (Failure.map (λ value → slots) (Flow.lift (Ignored.read middle))
     (ignoredFailure middle code suffix receipt))

  afterKnown : ∀ name index slots input code suffix → Slots.find name fields ≡ just index →
    Failure.Rejected (M.known index slots input) code suffix →
    Failure.Rejected (M.afterKey name slots input) code suffix
  afterKnown name index slots input code suffix selected receipt rewrite selected = receipt

  afterUnknown : ∀ name slots input code suffix → Slots.find name fields ≡ nothing →
    Failure.Rejected (M.ignored slots input) code suffix →
    Failure.Rejected (M.afterKey name slots input) code suffix
  afterUnknown name slots input code suffix absent receipt rewrite absent = receipt

  key : ∀ slots input code suffix →
    Failure.Rejected (Flow.Productive.result (Flow.fromJsonProductive (Atoms.string input))) code suffix →
    Failure.Rejected (Flow.Productive.result (M.member slots input)) code suffix
  key slots input code suffix receipt = Failure.bindProductive
    (Flow.fromJsonProductive (Atoms.string input))
    (λ name rest →
       M.afterKey (Decoded.text (String.values name)) slots rest)
    receipt

  afterKey : ∀ slots input name middle code suffix →
    Back.Returned (Flow.Productive.result (Flow.fromJsonProductive (Atoms.string input))) name middle →
    Failure.Rejected (M.afterKey (Decoded.text (String.values name)) slots middle) code suffix →
    Failure.Rejected (Flow.Productive.result (M.member slots input)) code suffix
  afterKey slots input name middle code suffix parsed receipt = Failure.afterProductive
    (Flow.fromJsonProductive (Atoms.string input))
    (λ name rest →
       M.afterKey (Decoded.text (String.values name)) slots rest)
    parsed receipt
