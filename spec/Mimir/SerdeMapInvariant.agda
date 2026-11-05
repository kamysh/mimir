{-# OPTIONS --safe #-}
-- Successful object visitors preserve all field predicates through arbitrary
-- member sequences and final default resolution.
import Mimir.FloatConversion
module Mimir.SerdeMapInvariant (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Bool using (true; false)
open import Data.List using (List)
open import Data.Product using (_,_; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
import Mimir.SerdeSequence as Sequence
import Mimir.SerdeSlots as Slots
import Mimir.SerdeSlotInvariant as I
import Mimir.SerdeMemberInvariant as MemberInvariantDependency
private
  module MemberInvariant = MemberInvariantDependency floatConversion
import Mimir.SerdeMap as MapDependency
private
  module Map = MapDependency floatConversion
import Mimir.SerdeLoop as Loop
import Mimir.SerdeLoopInvariant as Invariant
import Mimir.SerdeFlow as Flow
import Mimir.SerdeSuccess as S
import Mimir.JsonControls as Controls
module F = Flow.F

module Record (fields : List Sequence.Field) (readers : Slots.Readers fields)
  (properties : I.Predicates fields)
  (readersValid : ∀ index input → S.Ensures (properties index)
    (Flow.Productive.result (Slots.readerAt fields index readers input))) where
  module M = Map.Record fields readers
  module Member = MemberInvariant.Record fields readers properties readersValid
  Present = I.Present fields properties
  Valid = I.Valid fields properties
  module Inv = Invariant.Machine M.State (Slots.Slots fields) M.transition (λ state → Present (proj₂ state)) Present

  transition : ∀ state input → Present (proj₂ state) →
    S.Ensures Inv.Next (Loop.Step.result (M.transition state input))
  transition (first , slots) input holds with Controls.objectNext first input
  ... | Controls.C.failure code consumed remaining exact = tt
  ... | Controls.C.success false consumed remaining exact = holds
  ... | Controls.C.success true consumed remaining exact =
    S.map Present Inv.Next (λ value → inj₁ (false , value)) (λ value valid → valid)
      (Flow.prefix before (Flow.Productive.result (M.M.member slots remaining)))
      (S.prefix Present before (Flow.Productive.result (M.M.member slots remaining))
        (Member.member slots remaining holds))
    where before = F.cursor consumed remaining exact

  module Run = Inv.Laws transition

  resolve : ∀ slots input → Present slots → I.Defaults fields properties →
    S.Ensures Valid (M.resolve slots input)
  resolve slots input holds defaults with Slots.resolve fields slots in observed
  ... | inj₁ error = tt
  ... | inj₂ values = I.resolved properties (Slots.resolveSound fields slots values observed) holds defaults

  body : ∀ input → I.Defaults fields properties → S.Ensures Valid (M.body input)
  body input defaults = S.andThen Present Valid (M.Machine.read (true , Slots.empty fields) input) M.resolve
    (Run.read (true , Slots.empty fields) input (I.empty fields properties))
    (λ slots holds rest → resolve slots rest holds defaults)
