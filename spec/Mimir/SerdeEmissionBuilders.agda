{-# OPTIONS --safe #-}
-- Reusable omission and nested-array round-trip construction.
module Mimir.SerdeEmissionBuilders where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst)
open import Mimir.Text using (Text)
import Mimir.Validation as V
import Mimir.StructuredValue as JSON
import Mimir.RecordDecoding as Array
import Mimir.SerdeSequence as S
import Mimir.SerdeEmission as E
import Mimir.JudgeStatePrimitives as P
import Mimir.JudgeStateWire as W
import Mimir.JudgeStateBounds as B

optionComplete : ∀ {A : Set} decode (raw : JSON.Value) (value : A) → raw ≢ JSON.null →
  decode raw ≡ inj₂ value → P.option decode raw ≡ inj₂ (just value)
optionComplete decode JSON.null value nonnull observed = ⊥-elim (nonnull refl)
optionComplete decode (JSON.boolean raw) value nonnull observed rewrite observed = refl
optionComplete decode (JSON.string raw) value nonnull observed rewrite observed = refl
optionComplete decode (JSON.signed raw) value nonnull observed rewrite observed = refl
optionComplete decode (JSON.unsigned raw) value nonnull observed rewrite observed = refl
optionComplete decode (JSON.floating raw) value nonnull observed rewrite observed = refl
optionComplete decode (JSON.array raw) value nonnull observed rewrite observed = refl
optionComplete decode (JSON.object raw) value nonnull observed rewrite observed = refl

optional : ∀ {A : Set} {predicate : A → Set} name encode decode →
  (∀ value → encode value ≢ JSON.null) →
  (∀ value → predicate value → decode (encode value) ≡ inj₂ value) →
  ∀ value → B.Optional predicate value → ∀ {fields values input} → E.Emits fields values input →
  E.Emits (P.optional name A decode ∷ fields) (S.more value values) (W.optional name encode value ++ input)
optional name encode decode nonnull roundTrip nothing valid rest = E.omitted refl rest
optional name encode decode nonnull roundTrip (just value) valid rest =
  E.emitted (optionComplete decode (encode value) value (nonnull value) (roundTrip value valid)) rest

elements : ∀ {A : Set} {predicate : A → Set} encode decode →
  (∀ value → predicate value → decode (encode value) ≡ inj₂ value) →
  ∀ offset values → All predicate values → Array.readElementsFrom offset decode (map encode values) ≡ inj₂ values
elements encode decode roundTrip offset [] All.[] = refl
elements encode decode roundTrip offset (value ∷ values) (valid All.∷ rest)
  rewrite roundTrip value valid | elements encode decode roundTrip (suc offset) values rest = refl

array : ∀ {A : Set} {predicate : A → Set} encode decode →
  (∀ value → predicate value → decode (encode value) ≡ inj₂ value) →
  ∀ values → All predicate values → Array.readArray decode (JSON.array (map encode values)) ≡ inj₂ values
array encode decode roundTrip values valid = elements encode decode roundTrip 0 values valid

nonempty : ∀ {A : Set} {predicate : A → Set} name encode decode →
  (∀ value → predicate value → decode (encode value) ≡ inj₂ value) →
  ∀ value → All predicate value → ∀ {fields values input} → E.Emits fields values input →
  E.Emits (P.defaulted name (List A) (Array.readArray decode) [] ∷ fields) (S.more value values) (W.nonempty name encode value ++ input)
nonempty name encode decode roundTrip [] All.[] rest = E.omitted refl rest
nonempty name encode decode roundTrip (value ∷ values) valid rest = E.emitted (array encode decode roundTrip (value ∷ values) valid) rest

nonemptyText : ∀ name value {fields values input} → E.Emits fields values input →
  E.Emits (P.defaulted name Text JSON.asString [] ∷ fields) (S.more value values) (W.nonemptyText name value ++ input)
nonemptyText name [] rest = E.omitted refl rest
nonemptyText name (char ∷ chars) rest = E.emitted refl rest

optionalUniform : ∀ {A : Set} name encode decode →
  (∀ value → encode value ≢ JSON.null) → (∀ value → decode (encode value) ≡ inj₂ value) →
  ∀ value {fields values input} → E.Emits fields values input →
  E.Emits (P.optional name A decode ∷ fields) (S.more value values) (W.optional name encode value ++ input)
optionalUniform name encode decode nonnull roundTrip nothing rest = E.omitted refl rest
optionalUniform name encode decode nonnull roundTrip (just value) rest =
  E.emitted (optionComplete decode (encode value) value (nonnull value) (roundTrip value)) rest

nonemptyUniform : ∀ {A : Set} name encode decode → (∀ value → decode (encode value) ≡ inj₂ value) →
  ∀ value {fields values input} → E.Emits fields values input →
  E.Emits (P.defaulted name (List A) (Array.readArray decode) [] ∷ fields) (S.more value values) (W.nonempty name encode value ++ input)
nonemptyUniform name encode decode roundTrip [] rest = E.omitted refl rest
nonemptyUniform name encode decode roundTrip (value ∷ values) rest =
  E.emitted (Array.elementsRoundTrip encode decode roundTrip 0 (value ∷ values)) rest

optionalLast : ∀ {A : Set} {predicate : A → Set} name encode decode →
  (∀ value → encode value ≢ JSON.null) →
  (∀ value → predicate value → decode (encode value) ≡ inj₂ value) →
  ∀ value → B.Optional predicate value →
  E.Emits (P.optional name A decode ∷ []) (S.more value S.empty) (W.optional name encode value)
optionalLast name encode decode nonnull roundTrip value valid =
  subst (E.Emits (P.optional name _ decode ∷ []) (S.more value S.empty))
    (++-identityʳ (W.optional name encode value)) (optional name encode decode nonnull roundTrip value valid E.done)
