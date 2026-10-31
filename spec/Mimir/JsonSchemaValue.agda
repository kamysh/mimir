{-# OPTIONS --safe #-}
-- Total translation of admitted stored JSON into the request-schema value
-- model. Every key carries its decoded UTF-8 witness; arbitrary byte keys are
-- not coerced to text. Numeric variants and child/member order are retained.
module Mimir.JsonSchemaValue where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
open import Data.Product using (_×_; _,_)
import Mimir.JsonStoredValue as Stored
import Mimir.StructuredValue as Schema
import Mimir.JsonNumericValue as Numeric
import Mimir.DecodedText as Decoded
import Mimir.UnicodeText as Unicode
import Mimir.Text as Text
import Mimir.ByteKeyOrder as Key

mutual
  convert : ∀ value → Stored.Stored value → Schema.Value
  convert Stored.null Stored.null = Schema.null
  convert (Stored.boolean value) Stored.boolean = Schema.boolean value
  convert (Stored.number value) Stored.number = Numeric.decode value
  convert (Stored.string values) Stored.string = Schema.string (Decoded.text values)
  convert (Stored.array values) (Stored.array admitted) = Schema.array (convertArray values admitted)
  convert (Stored.object fields) (Stored.object sorted admitted) = Schema.object (convertFields fields admitted)

  convertArray : ∀ values → All Stored.Stored values → List Schema.Value
  convertArray [] All.[] = []
  convertArray (value ∷ rest) (admitted All.∷ remaining) = convert value admitted ∷ convertArray rest remaining

  convertFields : ∀ fields → All (λ { (name , value) → Stored.KeyValid name × Stored.Stored value }) fields →
    List (Text.Text × Schema.Value)
  convertFields [] All.[] = []
  convertFields ((name , value) ∷ rest) ((key , admitted) All.∷ remaining) =
    (Decoded.text (Stored.KeyValid.values key) , convert value admitted) ∷ convertFields rest remaining

mutual
  data Represents : Stored.Value → Schema.Value → Set where
    null : Represents Stored.null Schema.null
    boolean : ∀ value → Represents (Stored.boolean value) (Schema.boolean value)
    number : ∀ value → Represents (Stored.number value) (Numeric.decode value)
    string : ∀ {values text} → Unicode.Represents text values → Represents (Stored.string values) (Schema.string text)
    array : ∀ {values converted} → ArrayRepresents values converted → Represents (Stored.array values) (Schema.array converted)
    object : ∀ {fields converted} → FieldsRepresent fields converted → Represents (Stored.object fields) (Schema.object converted)

  data ArrayRepresents : List Stored.Value → List Schema.Value → Set where
    empty : ArrayRepresents [] []
    more : ∀ {value converted rest remaining} → Represents value converted → ArrayRepresents rest remaining →
      ArrayRepresents (value ∷ rest) (converted ∷ remaining)

  data FieldsRepresent : List (Key.Key × Stored.Value) → List (Text.Text × Schema.Value) → Set where
    empty : FieldsRepresent [] []
    more : ∀ {name text value converted rest remaining} → (key : Stored.KeyValid name) →
      Unicode.Represents text (Stored.KeyValid.values key) → Represents value converted →
      FieldsRepresent rest remaining → FieldsRepresent ((name , value) ∷ rest) ((text , converted) ∷ remaining)

mutual
  conversionRepresents : ∀ value admitted → Represents value (convert value admitted)
  conversionRepresents Stored.null Stored.null = null
  conversionRepresents (Stored.boolean value) Stored.boolean = boolean value
  conversionRepresents (Stored.number value) Stored.number = number value
  conversionRepresents (Stored.string values) Stored.string = string (Decoded.represents values)
  conversionRepresents (Stored.array values) (Stored.array admitted) = array (arrayRepresents values admitted)
  conversionRepresents (Stored.object fields) (Stored.object sorted admitted) = object (fieldsRepresent fields admitted)

  arrayRepresents : ∀ values admitted → ArrayRepresents values (convertArray values admitted)
  arrayRepresents [] All.[] = empty
  arrayRepresents (value ∷ rest) (admitted All.∷ remaining) = more
    (conversionRepresents value admitted) (arrayRepresents rest remaining)

  fieldsRepresent : ∀ fields admitted → FieldsRepresent fields (convertFields fields admitted)
  fieldsRepresent [] All.[] = empty
  fieldsRepresent ((name , value) ∷ rest) ((key , admitted) All.∷ remaining) = more key
    (Decoded.represents (Stored.KeyValid.values key)) (conversionRepresents value admitted) (fieldsRepresent rest remaining)
