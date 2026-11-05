{-# OPTIONS --safe #-}
-- Compact, ordered serialization for the integer/string/container subset
-- used by judge records. Floating values are explicitly outside this domain;
-- their general JSON codec remains a separate obligation.
module Mimir.JsonCompactRecords where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (nothing; just)
open import Data.Integer using (+_)
open import Data.Nat using (ℕ; _+_; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂)
open import Mimir.Bits using (Byte)
open import Mimir.Text using (Text)
import Mimir.StructuredValue as JSON
import Mimir.UnicodeText as Unicode
import Mimir.JsonSurface as Surface
import Mimir.JsonTextWriter as TextWriter
import Mimir.JsonIntegerWriter as IntegerWriter
import Mimir.JsonNumberWire as NumberWire
import Mimir.JsonString as String

mutual
  data Supported : JSON.Value → Set where
    null : Supported JSON.null
    boolean : ∀ value → Supported (JSON.boolean value)
    signed : ∀ value → Supported (JSON.signed value)
    unsigned : ∀ value → Supported (JSON.unsigned value)
    string : ∀ {value} → Unicode.Valid value → Supported (JSON.string value)
    array : ∀ {values} → All Supported values → Supported (JSON.array values)
    object : ∀ {fields} → All FieldSupported fields → Supported (JSON.object fields)

  FieldSupported : Text × JSON.Value → Set
  FieldSupported (name , value) = Unicode.Valid name × Supported value

emptyGap : Surface.Gap
emptyGap = Surface.gap [] All.[]

mutual
  render : ∀ value → Supported value → Surface.Value
  render JSON.null null = Surface.null
  render (JSON.boolean true) (boolean .true) = Surface.true
  render (JSON.boolean false) (boolean .false) = Surface.false
  render (JSON.signed value) (signed .value) = Surface.number (IntegerWriter.form value)
  render (JSON.unsigned value) (unsigned .value) = Surface.number (IntegerWriter.form (+ value))
  render (JSON.string value) (string valid) = Surface.string (TextWriter.render value valid)
  render (JSON.array []) (array All.[]) = Surface.array emptyGap nothing
  render (JSON.array (value ∷ values)) (array (valid All.∷ rest)) = Surface.array emptyGap (just (arrayEntries value values valid rest))
  render (JSON.object []) (object All.[]) = Surface.object emptyGap nothing
  render (JSON.object (entry ∷ fields)) (object (valid All.∷ rest)) = Surface.object emptyGap (just (objectEntries entry fields valid rest))

  arrayEntries : ∀ value values → Supported value → All Supported values → Surface.Separated Surface.Value
  arrayEntries value [] valid All.[] = Surface.last (render value valid) emptyGap
  arrayEntries value (next ∷ values) valid (nextValid All.∷ rest) =
    Surface.more (render value valid) emptyGap emptyGap (arrayEntries next values nextValid rest)

  renderField : ∀ entry → FieldSupported entry → Surface.Member
  renderField (name , value) (nameValid , valid) = Surface.member (TextWriter.render name nameValid) emptyGap emptyGap (render value valid)

  objectEntries : ∀ entry fields → FieldSupported entry → All FieldSupported fields → Surface.Separated Surface.Member
  objectEntries entry [] valid All.[] = Surface.last (renderField entry valid) emptyGap
  objectEntries entry (next ∷ fields) valid (nextValid All.∷ rest) =
    Surface.more (renderField entry valid) emptyGap emptyGap (objectEntries next fields nextValid rest)

bytes : ∀ value → Supported value → List Byte
bytes value valid = Surface.spell (render value valid)

-- Separate structural byte accounting, including every comma, colon and
-- delimiter. Scalar spelling is delegated to the established exact codecs.
mutual
  count : ∀ value → Supported value → ℕ
  count JSON.null null = 4
  count (JSON.boolean true) (boolean .true) = 4
  count (JSON.boolean false) (boolean .false) = 5
  count (JSON.signed value) (signed .value) = length (NumberWire.spell (IntegerWriter.form value))
  count (JSON.unsigned value) (unsigned .value) = length (NumberWire.spell (IntegerWriter.form (+ value)))
  count (JSON.string value) (string valid) = length (String.spellString (String.StringValue.body (TextWriter.render value valid)))
  count (JSON.array []) (array All.[]) = 2
  count (JSON.array (value ∷ values)) (array (valid All.∷ rest)) = suc (arrayCount value values valid rest)
  count (JSON.object []) (object All.[]) = 2
  count (JSON.object (entry ∷ fields)) (object (valid All.∷ rest)) = suc (objectCount entry fields valid rest)

  arrayCount : ∀ value values → Supported value → All Supported values → ℕ
  arrayCount value [] valid All.[] = count value valid + 1
  arrayCount value (next ∷ values) valid (nextValid All.∷ rest) = count value valid + suc (arrayCount next values nextValid rest)

  fieldCount : ∀ entry → FieldSupported entry → ℕ
  fieldCount (name , value) (nameValid , valid) =
    length (String.spellString (String.StringValue.body (TextWriter.render name nameValid))) + suc (count value valid)

  objectCount : ∀ entry fields → FieldSupported entry → All FieldSupported fields → ℕ
  objectCount entry [] valid All.[] = fieldCount entry valid + 1
  objectCount entry (next ∷ fields) valid (nextValid All.∷ rest) = fieldCount entry valid + suc (objectCount next fields nextValid rest)

mutual
  exactCount : ∀ value valid → length (bytes value valid) ≡ count value valid
  exactCount JSON.null null = refl
  exactCount (JSON.boolean true) (boolean .true) = refl
  exactCount (JSON.boolean false) (boolean .false) = refl
  exactCount (JSON.signed value) (signed .value) = refl
  exactCount (JSON.unsigned value) (unsigned .value) = refl
  exactCount (JSON.string value) (string valid) = refl
  exactCount (JSON.array []) (array All.[]) = refl
  exactCount (JSON.array (value ∷ values)) (array (valid All.∷ rest)) = cong suc (exactArrayCount value values valid rest)
  exactCount (JSON.object []) (object All.[]) = refl
  exactCount (JSON.object (entry ∷ fields)) (object (valid All.∷ rest)) = cong suc (exactObjectCount entry fields valid rest)

  exactArrayCount : ∀ value values valid rest →
    length (Surface.arrayBody (just (arrayEntries value values valid rest))) ≡ arrayCount value values valid rest
  exactArrayCount value [] valid All.[] = trans (length-++ (bytes value valid)) (cong (_+ 1) (exactCount value valid))
  exactArrayCount value (next ∷ values) valid (nextValid All.∷ rest) = trans (length-++ (bytes value valid))
    (cong₂ _+_ (exactCount value valid) (cong suc (exactArrayCount next values nextValid rest)))

  exactFieldCount : ∀ entry valid → length (Surface.spellMember (renderField entry valid)) ≡ fieldCount entry valid
  exactFieldCount (name , value) (nameValid , valid) =
    trans (length-++ (String.spellString (String.StringValue.body (TextWriter.render name nameValid))))
      (cong (λ count → length (String.spellString (String.StringValue.body (TextWriter.render name nameValid))) + count)
        (cong suc (exactCount value valid)))

  exactObjectCount : ∀ entry fields valid rest →
    length (Surface.objectBody (just (objectEntries entry fields valid rest))) ≡ objectCount entry fields valid rest
  exactObjectCount entry [] valid All.[] = trans (length-++ (Surface.spellMember (renderField entry valid)))
    (cong (_+ 1) (exactFieldCount entry valid))
  exactObjectCount entry (next ∷ fields) valid (nextValid All.∷ rest) = trans (length-++ (Surface.spellMember (renderField entry valid)))
    (cong₂ _+_ (exactFieldCount entry valid) (cong suc (exactObjectCount next fields nextValid rest)))
