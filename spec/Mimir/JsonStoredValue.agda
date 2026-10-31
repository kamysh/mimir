{-# OPTIONS --safe #-}
-- Normalize parsed trees to the default serde_json Value object behavior.
-- Keys use decoded UTF-8, duplicate writes keep the last value, and objects
-- iterate in strict byte-lexicographic key order.
module Mimir.JsonStoredValue where

open import Data.Bool using (Bool)
open import Data.Fin using (toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
open import Data.Nat using (_<_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Mimir.Bits using (Byte)
import Mimir.JsonString as String
import Mimir.UTF8Packet as Packet
import Mimir.UTF8Text as UTF8
import Mimir.JsonTree as Parsed
import Mimir.ByteKeyOrder as Key
import Mimir.OrderedObject as Objects

key : String.StringValue → Key.Key
key textValue = map toℕ (UTF8.encode (String.values textValue))

record KeyValid (name : Key.Key) : Set where
  constructor validKey
  field
    values : List Packet.Scalar
    exact : name ≡ map toℕ (UTF8.encode values)
    bounded : All (λ byte → byte < 256) name

byteCodesValid : (bytes : List Byte) → All (λ byte → byte < 256) (map toℕ bytes)
byteCodesValid [] = All.[]
byteCodesValid (byte ∷ rest) = toℕ<n byte All.∷ byteCodesValid rest

keyValid : ∀ textValue → KeyValid (key textValue)
keyValid textValue = validKey (String.values textValue) refl
  (byteCodesValid (UTF8.encode (String.values textValue)))

sameDecodedKey : ∀ first second → String.values first ≡ String.values second → key first ≡ key second
sameDecodedKey first second same = cong (λ scalars → map toℕ (UTF8.encode scalars)) same

data Value : Set where
  null : Value
  boolean : Bool → Value
  number : Parsed.ScalarNumber → Value
  string : List Packet.Scalar → Value
  array : List Value → Value
  object : List (Key.Key × Value) → Value

module Map = Objects.Object Value

data Stored : Value → Set where
  null : Stored null
  boolean : ∀ {value} → Stored (boolean value)
  number : ∀ {value} → Stored (number value)
  string : ∀ {value} → Stored (string value)
  array : ∀ {values} → All Stored values → Stored (array values)
  object : ∀ {fields} → Map.Sorted fields → All (λ { (name , value) → KeyValid name × Stored value }) fields → Stored (object fields)

mutual
  normalize : Parsed.Tree → Value
  normalize Parsed.null = null
  normalize (Parsed.boolean value) = boolean value
  normalize (Parsed.number value) = number value
  normalize (Parsed.string value) = string (String.values value)
  normalize (Parsed.array values) = array (normalizeArray values)
  normalize (Parsed.object fields) = object (Map.normalize (normalizeFields fields))

  normalizeArray : List Parsed.Tree → List Value
  normalizeArray [] = []
  normalizeArray (value ∷ rest) = normalize value ∷ normalizeArray rest

  normalizeFields : List (String.StringValue × Parsed.Tree) → Map.Fields
  normalizeFields [] = []
  normalizeFields ((name , value) ∷ rest) = (key name , normalize value) ∷ normalizeFields rest

mutual
  normalizedStored : ∀ tree → Stored (normalize tree)
  normalizedStored Parsed.null = null
  normalizedStored (Parsed.boolean value) = boolean
  normalizedStored (Parsed.number value) = number
  normalizedStored (Parsed.string value) = string
  normalizedStored (Parsed.array values) = array (normalizedArrayStored values)
  normalizedStored (Parsed.object fields) = object (Map.normalizedSorted (normalizeFields fields))
    (Map.loadAll (normalizeFields fields) [] (normalizedFieldsStored fields) All.[])

  normalizedArrayStored : ∀ values → All Stored (normalizeArray values)
  normalizedArrayStored [] = All.[]
  normalizedArrayStored (value ∷ rest) = normalizedStored value All.∷ normalizedArrayStored rest

  normalizedFieldsStored : ∀ fields →
    All (λ { (name , value) → KeyValid name × Stored value }) (normalizeFields fields)
  normalizedFieldsStored [] = All.[]
  normalizedFieldsStored ((name , value) ∷ rest) = (keyValid name , normalizedStored value) All.∷ normalizedFieldsStored rest
