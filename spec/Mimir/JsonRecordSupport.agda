{-# OPTIONS --safe #-}
-- Constructive support for compact record fields, including conditional
-- omission and nested lists. Static key validation uses a checked decision.
module Mimir.JsonRecordSupport where

open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary.Decidable.Core using (True; toWitness)
open import Mimir.Text using (Text)
import Mimir.UnicodeText as Unicode
import Mimir.StructuredValue as JSON
import Mimir.JsonCompactRecords as Compact
import Mimir.JudgeStateWire as W
import Mimir.JudgeStateBounds as Bounds

member : ∀ name → True (Unicode.valid? name) → ∀ value → Compact.Supported value → All Compact.FieldSupported (W.member name value)
member name valid value supported = (toWitness valid , supported) All.∷ All.[]

optional : ∀ {A : Set} {predicate : A → Set} name → True (Unicode.valid? name) →
  ∀ encode → (∀ value → predicate value → Compact.Supported (encode value)) →
  ∀ value → Bounds.Optional predicate value → All Compact.FieldSupported (W.optional name encode value)
optional name valid encode supported nothing admitted = All.[]
optional name valid encode supported (just value) admitted = member name valid (encode value) (supported value admitted)

optionalUniform : ∀ {A : Set} name → True (Unicode.valid? name) →
  (encode : A → JSON.Value) → (∀ value → Compact.Supported (encode value)) →
  ∀ value → All Compact.FieldSupported (W.optional name encode value)
optionalUniform name valid encode supported nothing = All.[]
optionalUniform name valid encode supported (just value) = member name valid (encode value) (supported value)

array : ∀ {A : Set} {predicate : A → Set} encode → (∀ value → predicate value → Compact.Supported (encode value)) →
  ∀ values → All predicate values → All Compact.Supported (map encode values)
array encode supported [] All.[] = All.[]
array encode supported (value ∷ values) (valid All.∷ rest) = supported value valid All.∷ array encode supported values rest

arrayUniform : ∀ {A : Set} (encode : A → JSON.Value) → (∀ value → Compact.Supported (encode value)) →
  ∀ values → All Compact.Supported (map encode values)
arrayUniform encode supported [] = All.[]
arrayUniform encode supported (value ∷ values) = supported value All.∷ arrayUniform encode supported values

nonemptyUniform : ∀ {A : Set} name → True (Unicode.valid? name) → (encode : A → JSON.Value) →
  (∀ value → Compact.Supported (encode value)) → ∀ values → All Compact.FieldSupported (W.nonempty name encode values)
nonemptyUniform name valid encode supported [] = All.[]
nonemptyUniform name valid encode supported (value ∷ values) =
  member name valid (JSON.array (map encode (value ∷ values))) (Compact.array (arrayUniform encode supported (value ∷ values)))

nonemptyText : ∀ name → True (Unicode.valid? name) → ∀ value → Unicode.Valid value → All Compact.FieldSupported (W.nonemptyText name value)
nonemptyText name valid [] admitted = All.[]
nonemptyText name valid (char ∷ chars) admitted = member name valid (JSON.string (char ∷ chars)) (Compact.string admitted)
