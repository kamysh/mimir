{-# OPTIONS --safe #-}
-- Successful object members compose through the map loop and default resolution.
import Mimir.FloatConversion
module Mimir.SerdeMapReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Bool using (true; false)
open import Data.Fin using (#_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.SerdeRecord as TypedRecordDependency
private
  module TypedRecord = TypedRecordDependency floatConversion
import Mimir.SignedMachine as Machine
import Mimir.Validation as V
import Mimir.SerdeSequence as Sequence
import Mimir.SerdeSlots as Slots
import Mimir.SerdeMap as MapDependency
private
  module Map = MapDependency floatConversion
import Mimir.SerdeFlow as Flow
import Mimir.SerdeLoop as Loop
import Mimir.SerdeLoopReadBack as LoopBackDependency
private
  module LoopBack = LoopBackDependency floatConversion
import Mimir.SerdeReadBack as Back
import Mimir.SerdeReadBackComposition as ComposeDependency
private
  module Compose = ComposeDependency floatConversion
import Mimir.JsonControls as Controls

firstControl : ∀ rest → Controls.objectNext true ((# 34) ∷ rest) ≡
  Controls.C.success true [] ((# 34) ∷ rest) refl
firstControl rest = refl

laterControl : ∀ rest → Controls.objectNext false ((# 44) ∷ (# 34) ∷ rest) ≡
  Controls.C.success true ((# 44) ∷ []) ((# 34) ∷ rest) refl
laterControl rest = refl

module Record (fields : List Sequence.Field) (readers : Slots.Readers fields) where
  private
    module M = Map.Record fields readers
    module Steps = LoopBack.Machine M.State (Slots.Slots fields) M.transition

  closed : ∀ first slots suffix →
    Back.Returned (M.Machine.read (first , slots) ((# 125) ∷ suffix)) slots ((# 125) ∷ suffix)
  closed first slots suffix = Steps.finish (first , slots) (# 125 ∷ suffix) slots
    (# 125 ∷ suffix)
    (Back.returned (Flow.F.initial (# 125 ∷ suffix)) refl refl)

  advance : ∀ first slots input consumed middle exact output suffix →
    Controls.objectNext first input ≡ Controls.C.success true consumed middle exact →
    Back.Returns (M.M.member slots) middle output suffix →
    Back.Returned (Loop.Step.result (M.transition (first , slots) input)) (inj₁ (false , output)) suffix
  advance first slots input consumed middle exact output suffix selected receipt
    rewrite selected with M.M.member slots middle | receipt
  ... | Flow.productive result progress | evidence = Compose.map (λ value → inj₁ (false , value))
    (Compose.prefix (Flow.F.cursor consumed middle exact) evidence)

  next : ∀ first slots input consumed middle exact output after result suffix →
    Controls.objectNext first input ≡ Controls.C.success true consumed middle exact →
    Back.Returns (M.M.member slots) middle output after →
    Back.Returned (M.Machine.read (false , output) after) result suffix →
    Back.Returned (M.Machine.read (first , slots) input) result suffix
  next first slots input consumed middle exact output after result suffix selected head tail = Steps.next (first , slots) input (false , output) after result
    suffix
    (advance first slots input consumed middle exact output after
     selected head)
    tail

  resolve : ∀ slots values suffix → Slots.Resolved fields slots values →
    Back.Returned (M.resolve slots suffix) values suffix
  resolve slots values suffix resolved rewrite Slots.resolveComplete resolved = Back.returned (Flow.F.initial suffix) refl refl

  body : ∀ input slots values suffix →
    Back.Returned (M.Machine.read (true , Slots.empty fields) input) slots suffix →
    Slots.Resolved fields slots values → Back.Returned (M.body input) values suffix
  body input slots values suffix receipt resolved = Compose.andThen (M.Machine.read (true , Slots.empty fields) input)
    M.resolve receipt (resolve slots values suffix resolved)

module Parser (checks : Machine.OverflowChecks) (fields : List Sequence.Field)
  (readers : ℕ → Slots.Readers fields) (expected : V.Fault) where
  private module P = TypedRecord.Parser checks fields readers expected

  closeContainer : ∀ allowance rest values suffix →
    Back.Returned (P.mapBody allowance rest) values ((# 125) ∷ suffix) →
    Back.Returns (P.read (suc allowance)) ((# 123) ∷ rest) values suffix
  closeContainer allowance rest values suffix receipt = Compose.noWhitespace (P.dispatch (suc allowance)) (# 123) rest
    (λ ())
    (Compose.container (# 123) rest Controls.objectEnd receipt
     (# 125 ∷ []) suffix refl refl)
