{-# OPTIONS --safe #-}
-- Current-review reads use the header and stored review payload.
module Mimir.LearningHistoryWire where

open import Data.Bool using (true; false; _∧_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Mimir.UUIDGroups using (UUID; _≟UUID_)
open import Data.Integer using (ℤ)
import Data.Integer.Properties as Integer
open import Relation.Nullary using (does; yes; no)
import Mimir.StructuredValue as V

record Head : Set where
  constructor head
  field identity : UUID; revision reviewRevision reviewedRevision : ℤ

record Row : Set where
  constructor row
  -- createdAt is UTC nanoseconds; revisions remain ordinary integers.
  field experience : UUID; revision sourceRevision createdAt : ℤ; payload : V.Value

record Current : Set where
  constructor current
  field revision reviewRevision reviewedRevision : ℤ; review : Maybe V.Value

record Database : Set where
  field heads : List Head; sourceRows reviewRows : List Row

find : UUID → List Head → Maybe Head
find id [] = nothing
find id (header ∷ rest) with id ≟UUID Head.identity header
... | yes _ = just header
... | no _ = find id rest

joined : Head → List Row → Maybe V.Value
joined header [] = nothing
joined header (item ∷ rest) with does (Head.identity header ≟UUID Row.experience item) ∧
  does (Head.reviewRevision header Integer.≟ Row.revision item) ∧
  does (Head.revision header Integer.≟ Row.sourceRevision item)
... | true = just (Row.payload item)
... | false = joined header rest

readCurrent : UUID → Database → Maybe Current
readCurrent id db with find id (Database.heads db)
... | nothing = nothing
... | just header = just (current (Head.revision header) (Head.reviewRevision header)
    (Head.reviewedRevision header) (joined header (Database.reviewRows db)))
