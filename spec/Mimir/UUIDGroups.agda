{-# OPTIONS --safe #-}
-- UUIDs are opaque outside this module; clients can only compare them.
module Mimir.UUIDGroups where

open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false)
import Data.String as String
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_)

abstract
  UUID : Set
  UUID = String.String

  _≟UUID_ : (a b : UUID) → Dec (a ≡ b)
  _≟UUID_ = String._≟_

member : UUID → List UUID → Bool
member id [] = false
member id (other ∷ rest) with id ≟UUID other
... | yes _ = true
... | no _ = member id rest
