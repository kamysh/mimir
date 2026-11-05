{-# OPTIONS --safe #-}
-- Public history and current-review reads preserve arbitrary stored JSONB.
-- They do not deserialize historical payloads using the current schema;
-- reading a review header never reads the experience payload.
module Mimir.LearningHistoryWire where

open import Data.Bool using (true; false; _∧_)
open import Data.List using (List; []; _∷_; map; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Data.Integer using (ℤ)
import Data.Integer.Properties as Integer
open import Relation.Nullary using (does; yes; no)
import Mimir.StructuredValue as V

data Kind : Set where sources reviews : Kind

record Head : Set where
  constructor head
  field identity : ℕ; revision reviewRevision reviewedRevision : ℤ

record Row : Set where
  constructor row
  field experience : ℕ; revision sourceRevision createdAt : ℤ; payload : V.Value

record Entry : Set where
  constructor entry
  field revision : ℤ; payload : V.Value; createdAt : ℤ

record Current : Set where
  constructor current
  field revision reviewRevision reviewedRevision : ℤ; review : Maybe V.Value

record Database : Set where
  field heads : List Head; sourceRows reviewRows : List Row

find : ℕ → List Head → Maybe Head
find id [] = nothing
find id (header ∷ rest) with id ≟ Head.identity header
... | yes _ = just header
... | no _ = find id rest

joined : Head → List Row → Maybe V.Value
joined header [] = nothing
joined header (item ∷ rest) with does (Head.identity header ≟ Row.experience item) ∧
  does (Head.reviewRevision header Integer.≟ Row.revision item) ∧
  does (Head.revision header Integer.≟ Row.sourceRevision item)
... | true = just (Row.payload item)
... | false = joined header rest

readCurrent : ℕ → Database → Maybe Current
readCurrent id db with find id (Database.heads db)
... | nothing = nothing
... | just header = just (current (Head.revision header) (Head.reviewRevision header)
    (Head.reviewedRevision header) (joined header (Database.reviewRows db)))

insert : Entry → List Entry → List Entry
insert item [] = item ∷ []
insert item (next ∷ rest) with Entry.revision item Integer.≤? Entry.revision next
... | yes _ = item ∷ next ∷ rest
... | no _ = next ∷ insert item rest

sort : List Entry → List Entry
sort [] = []
sort (item ∷ rest) = insert item (sort rest)

selected : Kind → Database → List Row
selected sources = Database.sourceRows
selected reviews = Database.reviewRows

readHistory : Kind → ℕ → Database → List Entry
readHistory kind id db = sort (map (λ item → entry (Row.revision item) (Row.payload item) (Row.createdAt item))
  (filterᵇ (λ item → does (id ≟ Row.experience item)) (selected kind db)))
