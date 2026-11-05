{-# OPTIONS --safe #-}
-- Raw-reader counterparts of the existing schema emission/omission builders.
import Mimir.FloatConversion
module Mimir.SerdeRawEmissionBuilders (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable.Core using (True)
open import Relation.Binary.PropositionalEquality using (refl)
open import Mimir.Text using (Text)
import Mimir.UnicodeText as Unicode
import Mimir.StructuredValue as JSON
import Mimir.JsonCompactRecords as Compact
import Mimir.JsonRecordSupport as Support
import Mimir.JsonObjectReadBack as Encoding
import Mimir.RecordDecoding as Array
import Mimir.JudgeStatePrimitives as P
import Mimir.JudgeStateWire as W
import Mimir.JudgeStateBounds as B
import Mimir.SerdeFlow as Flow
import Mimir.SerdeReadBack as Back
import Mimir.SerdeRawEmission as EDependency
private
  module E = EDependency floatConversion
import Mimir.Validation as V

optional : ∀ {A : Set} {predicate : A → Set} name (nameValid : True (Unicode.valid? name))
  (encode : A → JSON.Value) (decode : JSON.Value → V.Fault ⊎ A) (reader : Flow.Parser (Maybe A))
  (supported : ∀ value → predicate value → Compact.Supported (encode value)) →
  (∀ value valid suffix → Encoding.Delimited suffix →
    Back.Returns reader (Compact.bytes (encode value) (supported value valid) ++ suffix) (just value) suffix) →
  ∀ value (valid : B.Optional predicate value) {fields readers values input inputValid} →
  E.Emits fields readers values input inputValid →
  E.Emits (P.optional name A decode ∷ fields) (reader , readers) (value , values)
    (W.optional name encode value ++ input)
    (++⁺ (Support.optional name nameValid encode supported value valid) inputValid)
optional name nameValid encode decode reader supported read nothing valid tail = E.omitted refl tail
optional name nameValid encode decode reader supported read (just value) valid tail = E.emitted (read value valid) tail

optionalUniform : ∀ {A : Set} name (nameValid : True (Unicode.valid? name))
  (encode : A → JSON.Value) (decode : JSON.Value → V.Fault ⊎ A) (reader : Flow.Parser (Maybe A))
  (supported : ∀ value → Compact.Supported (encode value)) →
  (∀ value suffix → Encoding.Delimited suffix →
    Back.Returns reader (Compact.bytes (encode value) (supported value) ++ suffix) (just value) suffix) →
  ∀ value {fields readers values input inputValid} → E.Emits fields readers values input inputValid →
  E.Emits (P.optional name A decode ∷ fields) (reader , readers) (value , values)
    (W.optional name encode value ++ input)
    (++⁺ (Support.optionalUniform name nameValid encode supported value) inputValid)
optionalUniform name nameValid encode decode reader supported read nothing tail = E.omitted refl tail
optionalUniform name nameValid encode decode reader supported read (just value) tail = E.emitted (read value) tail

optionalLast : ∀ {A : Set} {predicate : A → Set} name (nameValid : True (Unicode.valid? name))
  (encode : A → JSON.Value) (decode : JSON.Value → V.Fault ⊎ A) (reader : Flow.Parser (Maybe A))
  (supported : ∀ value → predicate value → Compact.Supported (encode value)) →
  (∀ value valid suffix → Encoding.Delimited suffix →
    Back.Returns reader (Compact.bytes (encode value) (supported value valid) ++ suffix) (just value) suffix) →
  ∀ value (valid : B.Optional predicate value) →
  E.Emits (P.optional name A decode ∷ []) (reader , tt) (value , tt)
    (W.optional name encode value) (Support.optional name nameValid encode supported value valid)
optionalLast name nameValid encode decode reader supported read nothing valid = E.omitted refl E.done
optionalLast name nameValid encode decode reader supported read (just value) valid = E.emitted (read value valid) E.done

optionalBounded : ∀ {A : Set} {predicate : A → Set} name (nameValid : True (Unicode.valid? name))
  (encode : A → JSON.Value) (decode : JSON.Value → V.Fault ⊎ A) (reader : Flow.Parser (Maybe A))
  (supported : ∀ value → Compact.Supported (encode value)) →
  (∀ value → predicate value → ∀ suffix → Encoding.Delimited suffix →
    Back.Returns reader (Compact.bytes (encode value) (supported value) ++ suffix) (just value) suffix) →
  ∀ value (valid : B.Optional predicate value) {fields readers values input inputValid} →
  E.Emits fields readers values input inputValid →
  E.Emits (P.optional name A decode ∷ fields) (reader , readers) (value , values)
    (W.optional name encode value ++ input)
    (++⁺ (Support.optionalUniform name nameValid encode supported value) inputValid)
optionalBounded name nameValid encode decode reader supported read (just value) valid tail = E.emitted (read value valid) tail
optionalBounded name nameValid encode decode reader supported read nothing valid tail = E.omitted refl tail

optionalBoundedLast : ∀ {A : Set} {predicate : A → Set} name (nameValid : True (Unicode.valid? name))
  (encode : A → JSON.Value) (decode : JSON.Value → V.Fault ⊎ A) (reader : Flow.Parser (Maybe A))
  (supported : ∀ value → Compact.Supported (encode value)) →
  (∀ value → predicate value → ∀ suffix → Encoding.Delimited suffix →
    Back.Returns reader (Compact.bytes (encode value) (supported value) ++ suffix) (just value) suffix) →
  ∀ value (valid : B.Optional predicate value) →
  E.Emits (P.optional name A decode ∷ []) (reader , tt) (value , tt)
    (W.optional name encode value) (Support.optionalUniform name nameValid encode supported value)
optionalBoundedLast name nameValid encode decode reader supported read (just value) valid = E.emitted (read value valid) E.done
optionalBoundedLast name nameValid encode decode reader supported read nothing valid = E.omitted refl E.done

optionalChecked : ∀ {A : Set} {writePredicate readPredicate : A → Set}
  name (nameValid : True (Unicode.valid? name))
  (encode : A → JSON.Value) (decode : JSON.Value → V.Fault ⊎ A) (reader : Flow.Parser (Maybe A))
  (supported : ∀ value → writePredicate value → Compact.Supported (encode value)) →
  (∀ value (valid : writePredicate value) → readPredicate value → ∀ suffix → Encoding.Delimited suffix →
    Back.Returns reader (Compact.bytes (encode value) (supported value valid) ++ suffix) (just value) suffix) →
  ∀ value (writeValid : B.Optional writePredicate value) (readValid : B.Optional readPredicate value)
    {fields readers values input inputValid} → E.Emits fields readers values input inputValid →
  E.Emits (P.optional name A decode ∷ fields) (reader , readers) (value , values)
    (W.optional name encode value ++ input)
    (++⁺ (Support.optional name nameValid encode supported value writeValid) inputValid)
optionalChecked name nameValid encode decode reader supported read (just value) writeValid readValid tail = E.emitted (read value writeValid readValid) tail
optionalChecked name nameValid encode decode reader supported read nothing writeValid readValid tail = E.omitted refl tail

nonempty : ∀ {A : Set} {predicate : List A → Set} name (nameValid : True (Unicode.valid? name))
  (encode : A → JSON.Value) (decode : JSON.Value → V.Fault ⊎ A) (reader : Flow.Parser (List A))
  (supported : ∀ value → Compact.Supported (encode value)) →
  (∀ values → predicate values → ∀ suffix → Encoding.Delimited suffix →
    Back.Returns reader
      (Compact.bytes (JSON.array (map encode values))
        (Compact.array (Support.arrayUniform encode supported values)) ++ suffix) values suffix) →
  ∀ values → predicate values → ∀ {fields readers rest input inputValid} →
  E.Emits fields readers rest input inputValid →
  E.Emits (P.defaulted name (List A) (Array.readArray decode) [] ∷ fields)
    (reader , readers) (values , rest) (W.nonempty name encode values ++ input)
    (++⁺ (Support.nonemptyUniform name nameValid encode supported values) inputValid)
nonempty name nameValid encode decode reader supported read [] valid tail = E.omitted refl tail
nonempty name nameValid encode decode reader supported read (value ∷ values) valid tail = E.emitted (read (value ∷ values) valid) tail

nonemptyText : ∀ name (nameValid : True (Unicode.valid? name)) (reader : Flow.Parser Text) →
  (∀ value valid suffix → Encoding.Delimited suffix →
    Back.Returns reader (Compact.bytes (JSON.string value) (Compact.string valid) ++ suffix) value suffix) →
  ∀ value (valid : Unicode.Valid value) {fields readers values input inputValid} →
  E.Emits fields readers values input inputValid →
  E.Emits (P.defaulted name Text JSON.asString [] ∷ fields) (reader , readers) (value , values)
    (W.nonemptyText name value ++ input) (++⁺ (Support.nonemptyText name nameValid value valid) inputValid)
nonemptyText name nameValid reader read [] valid tail = E.omitted refl tail
nonemptyText name nameValid reader read (char ∷ chars) valid tail = E.emitted (read (char ∷ chars) valid) tail
