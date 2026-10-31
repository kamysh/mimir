{-# OPTIONS --safe #-}
-- Raw map-form struct decoding. Syntax controls, typed field readers and
-- default resolution execute in source order; object cleanup is done by the
-- surrounding container parser.
import Mimir.FloatConversion
module Mimir.SerdeMap (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.SerdeSequence as Sequence
import Mimir.SerdeSlots as Slots
import Mimir.SerdeMember as MemberDependency
private
  module Member = MemberDependency floatConversion
import Mimir.SerdeFlow as Flow
import Mimir.SerdeLoop as Loop
import Mimir.JsonControls as Controls
module F = Flow.F

module Record (fields : List Sequence.Field) (readers : Slots.Readers fields) where
  module M = Member.Record fields readers
  State : Set
  State = Bool × Slots.Slots fields

  transition : State → ∀ input → Loop.Step State (Slots.Slots fields) input
  transition (first , slots) input with Controls.objectNext first input
  ... | Controls.C.failure code consumed remaining exact =
    Loop.step (Flow.lift (Controls.C.failure code consumed remaining exact)) tt
  ... | Controls.C.success false consumed remaining exact =
    Loop.step (Flow.ordinary (F.success (inj₂ slots) (F.cursor consumed remaining exact))) tt
  ... | Controls.C.success true consumed remaining exact with M.member slots remaining
  ... | Flow.productive result progress = Loop.continuing (false ,_)
    (Flow.productive (Flow.prefix before result) (Flow.preserveProgress before result progress))
    where before = F.cursor consumed remaining exact

  module Machine = Loop.Machine State (Slots.Slots fields) transition

  resolve : Slots.Slots fields → ∀ input → Flow.Result (Slots.Values fields) input
  resolve slots input with Slots.resolve fields slots
  ... | inj₁ error = Flow.reject error input
  ... | inj₂ values = Flow.done values input

  body : ∀ input → Flow.Result (Slots.Values fields) input
  body input = Flow.andThen (Machine.read (true , Slots.empty fields) input) resolve

  boundaryStops : ∀ first slots input consumed remaining exact →
    Controls.objectNext first input ≡ Controls.C.success false consumed remaining exact →
    Loop.Step.result (transition (first , slots) input) ≡
      Flow.ordinary (F.success (inj₂ slots) (F.cursor consumed remaining exact))
  boundaryStops first slots input consumed remaining exact boundary rewrite boundary = refl

  syntaxStops : ∀ first slots input code consumed remaining exact →
    Controls.objectNext first input ≡ Controls.C.failure code consumed remaining exact →
    Loop.Step.result (transition (first , slots) input) ≡
      Flow.lift (Controls.C.failure code consumed remaining exact)
  syntaxStops first slots input code consumed remaining exact failed rewrite failed = refl

  defaultsSound : ∀ slots values input → Slots.Resolved fields slots values →
    resolve slots input ≡ Flow.done values input
  defaultsSound slots values input resolved rewrite Slots.resolveComplete resolved = refl

  missingStops : ∀ slots input error → Slots.resolve fields slots ≡ inj₁ error →
    resolve slots input ≡ Flow.reject error input
  missingStops slots input error failed rewrite failed = refl
