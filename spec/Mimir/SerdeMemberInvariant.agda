{-# OPTIONS --safe #-}
-- A typed field insertion preserves every field predicate when the selected
-- reader proves its own predicate. Unknown values cannot alter present fields.
import Mimir.FloatConversion
module Mimir.SerdeMemberInvariant (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.List using (List)
open import Data.Maybe using (nothing; just)
open import Data.Unit using (⊤; tt)
import Mimir.SerdeSequence as Sequence
import Mimir.SerdeSlots as Slots
import Mimir.SerdeSlotInvariant as I
import Mimir.SerdeMember as MemberDependency
private
  module Member = MemberDependency floatConversion
import Mimir.SerdeSuccess as S
import Mimir.SerdeFlow as Flow
import Mimir.JsonControls as Controls
import Mimir.JsonIgnoredRun as IgnoredDependency
private
  module Ignored = IgnoredDependency floatConversion
import Mimir.JsonAtoms as AtomsDependency
private
  module Atoms = AtomsDependency floatConversion
import Mimir.JsonString as String
import Mimir.DecodedText as Decoded

module Record (fields : List Sequence.Field) (readers : Slots.Readers fields)
  (properties : I.Predicates fields)
  (readersValid : ∀ index input → S.Ensures (properties index)
    (Flow.Productive.result (Slots.readerAt fields index readers input))) where
  module M = Member.Record fields readers
  Present = I.Present fields properties

  known : ∀ index slots input → Present slots → S.Ensures Present (M.known index slots input)
  known index slots input holds with Slots.get fields index slots
  ... | just previous = tt
  ... | nothing = S.andThen (λ _ → ⊤) Present (Flow.lift (Controls.colon input))
    (λ unit rest → Flow.map (λ value → Slots.put fields index value slots)
      (Flow.Productive.result (Slots.readerAt fields index readers rest)))
    (S.trivial (Flow.lift (Controls.colon input)))
    (λ unit _ rest → S.map (properties index) Present (λ value → Slots.put fields index value slots)
      (λ value valid → I.put fields properties index value slots holds valid)
      (Flow.Productive.result (Slots.readerAt fields index readers rest)) (readersValid index rest))

  ignored : ∀ slots input → Present slots → S.Ensures Present (M.ignored slots input)
  ignored slots input holds = S.andThen (λ _ → ⊤) Present (Flow.lift (Controls.colon input))
    (λ unit rest → Flow.map (λ value → slots) (Flow.lift (Ignored.read rest)))
    (S.trivial (Flow.lift (Controls.colon input)))
    (λ unit _ rest → S.map (λ _ → ⊤) Present (λ _ → slots) (λ _ _ → holds)
      (Flow.lift (Ignored.read rest)) (S.trivial (Flow.lift (Ignored.read rest))))

  afterKey : ∀ name slots input → Present slots → S.Ensures Present (M.afterKey name slots input)
  afterKey name slots input holds with Slots.find name fields
  ... | just index = known index slots input holds
  ... | nothing = ignored slots input holds

  member : ∀ slots input → Present slots → S.Ensures Present (Flow.Productive.result (M.member slots input))
  member slots input holds = S.andThen (λ _ → ⊤) Present
    (Flow.Productive.result (Flow.fromJsonProductive (Atoms.string input)))
    (λ key rest → M.afterKey (Decoded.text (String.values key)) slots rest)
    (S.trivial (Flow.Productive.result (Flow.fromJsonProductive (Atoms.string input))))
    (λ key _ rest → afterKey (Decoded.text (String.values key)) slots rest holds)
