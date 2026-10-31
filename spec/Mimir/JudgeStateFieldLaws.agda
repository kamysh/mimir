{-# OPTIONS --safe #-}
-- Decoder/default invariants composed into concrete state-field rules.
module Mimir.JudgeStateFieldLaws where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _≤_)
open import Data.Integer using (ℤ; +_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
import Mimir.StructuredValue as JSON
import Mimir.Validation as V
import Mimir.RecordDecoding as Array
import Mimir.JudgeStatePrimitives as P
import Mimir.JudgeStateBounds as B
import Mimir.SerdeObtained as O
import Mimir.SerdeSequence as S

unsigned : ∀ maximum raw value → P.uint maximum raw ≡ inj₂ value → value ≤ maximum
unsigned maximum raw value observed = JSON.integerInRange (P.uintSound maximum raw value observed)

signed : ∀ raw value → P.signed raw ≡ inj₂ value → P.I64.InRange value
signed (JSON.signed number) value observed with P.signedNumberSound number value observed
... | refl , bounded = bounded
signed (JSON.unsigned number) value observed with P.signedNumberSound (+ number) value observed
... | refl , bounded = bounded
signed JSON.null value ()
signed (JSON.boolean raw) value ()
signed (JSON.string raw) value ()
signed (JSON.floating raw) value ()
signed (JSON.array raw) value ()
signed (JSON.object raw) value ()

optionResult : ∀ {A : Set} {predicate : A → Set} (result : V.Fault ⊎ A) value →
  (∀ actual → result ≡ inj₂ actual → predicate actual) →
  P.optionResult result ≡ inj₂ value → B.Optional predicate value
optionResult (inj₁ failure) value sound ()
optionResult (inj₂ actual) .(just actual) sound refl = sound actual refl

option : ∀ {A : Set} {predicate : A → Set} decode →
  (∀ raw value → decode raw ≡ inj₂ value → predicate value) →
  ∀ raw value → P.option decode raw ≡ inj₂ value → B.Optional predicate value
option decode sound JSON.null .nothing refl = tt
option decode sound raw@(JSON.boolean _) value observed = optionResult (decode raw) value (sound raw) observed
option decode sound raw@(JSON.string _) value observed = optionResult (decode raw) value (sound raw) observed
option decode sound raw@(JSON.signed _) value observed = optionResult (decode raw) value (sound raw) observed
option decode sound raw@(JSON.unsigned _) value observed = optionResult (decode raw) value (sound raw) observed
option decode sound raw@(JSON.floating _) value observed = optionResult (decode raw) value (sound raw) observed
option decode sound raw@(JSON.array _) value observed = optionResult (decode raw) value (sound raw) observed
option decode sound raw@(JSON.object _) value observed = optionResult (decode raw) value (sound raw) observed

elements : ∀ {A : Set} {predicate : A → Set} decode →
  (∀ raw value → decode raw ≡ inj₂ value → predicate value) →
  ∀ offset raw values → Array.readElementsFrom offset decode raw ≡ inj₂ values → All predicate values
elements decode sound offset [] .[] refl = All.[]
elements decode sound offset (raw ∷ input) values observed with decode raw in decoded
... | inj₁ failure with observed
...   | ()
elements decode sound offset (raw ∷ input) values observed | inj₂ value
  with Array.readElementsFrom (suc offset) decode input in later
... | inj₁ failure with observed
...   | ()
elements decode sound offset (raw ∷ input) .(value ∷ values) refl | inj₂ value | inj₂ values =
  sound raw value decoded All.∷ elements decode sound (suc offset) input values later

array : ∀ {A : Set} {predicate : A → Set} decode →
  (∀ raw value → decode raw ≡ inj₂ value → predicate value) →
  ∀ raw values → Array.readArray decode raw ≡ inj₂ values → All predicate values
array decode sound (JSON.array raw) values observed = elements decode sound 0 raw values observed
array decode sound JSON.null values ()
array decode sound (JSON.boolean raw) values ()
array decode sound (JSON.string raw) values ()
array decode sound (JSON.signed raw) values ()
array decode sound (JSON.unsigned raw) values ()
array decode sound (JSON.floating raw) values ()
array decode sound (JSON.object raw) values ()

required : ∀ {A : Set} {predicate : A → Set} name decode →
  (∀ raw value → decode raw ≡ inj₂ value → predicate value) → O.Sound (P.required name A decode) predicate
required name decode sound = O.sound sound (λ value ())

defaulted : ∀ {A : Set} {predicate : A → Set} name decode fallback →
  (∀ raw value → decode raw ≡ inj₂ value → predicate value) → predicate fallback →
  O.Sound (P.defaulted name A decode fallback) predicate
defaulted name decode fallback sound valid = O.sound sound (λ { .fallback refl → valid })

optional : ∀ {A : Set} {predicate : A → Set} name decode →
  (∀ raw value → decode raw ≡ inj₂ value → predicate value) → O.Sound (P.optional name A decode) (B.Optional predicate)
optional name decode sound = defaulted name (P.option decode) nothing (option decode sound) tt

recordBound : ∀ {A : Set} {predicate : A → Set} fields (build : S.Values fields → A) (rules : O.Rules fields) →
  (∀ values → O.Satisfied rules values → predicate (build values)) →
  ∀ raw value → P.recordDecoder fields build raw ≡ inj₂ value → predicate value
recordBound fields build rules project raw value observed with P.recordSuccess fields build raw value observed
... | values , admitted , exact = subst _ exact (project values (O.satisfied rules (O.fromStruct admitted)))
