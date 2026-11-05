{-# OPTIONS --safe #-}
-- A structural nesting certificate, independent of parser execution.
module Mimir.JsonTreeBounds where

open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_; z≤n; s≤s)
open import Data.Nat.Properties using (⊔-lub; ≤-trans; m≤m⊔n; m≤n⊔m)
open import Data.Product using (_×_; _,_; proj₂)
open import Mimir.JsonTree
import Mimir.JsonString as String
import Mimir.NumericTokens as Numeric
import Mimir.FloatValue as A

mutual
  depth : Tree → ℕ
  depth null = 0
  depth (boolean value) = 0
  depth (number value) = 0
  depth (string value) = 0
  depth (array values) = suc (arrayDepth values)
  depth (object members) = suc (objectDepth members)

  arrayDepth : List Tree → ℕ
  arrayDepth [] = 0
  arrayDepth (value ∷ rest) = depth value ⊔ arrayDepth rest

  objectDepth : List (String.StringValue × Tree) → ℕ
  objectDepth [] = 0
  objectDepth ((key , value) ∷ rest) = depth value ⊔ objectDepth rest

data Within : ℕ → Tree → Set where
  null : ∀ {allowance} → Within allowance null
  boolean : ∀ {allowance value} → Within allowance (boolean value)
  number : ∀ {allowance value} → Within allowance (number value)
  string : ∀ {allowance value} → Within allowance (string value)
  array : ∀ {allowance values} → All (Within allowance) values → Within (suc allowance) (array values)
  object : ∀ {allowance members} → All (λ member → Within allowance (proj₂ member)) members → Within (suc allowance) (object members)

mutual
  boundedDepth : ∀ {allowance tree} → Within allowance tree → depth tree ≤ allowance
  boundedDepth null = z≤n
  boundedDepth boolean = z≤n
  boundedDepth number = z≤n
  boundedDepth string = z≤n
  boundedDepth (array children) = s≤s (arrayBound children)
  boundedDepth (object children) = s≤s (objectBound children)

  arrayBound : ∀ {allowance values} → All (Within allowance) values → arrayDepth values ≤ allowance
  arrayBound All.[] = z≤n
  arrayBound (first All.∷ rest) = ⊔-lub (boundedDepth first) (arrayBound rest)

  objectBound : ∀ {allowance members} → All (λ member → Within allowance (proj₂ member)) members → objectDepth members ≤ allowance
  objectBound All.[] = z≤n
  objectBound {members = (key , value) ∷ members} (first All.∷ rest) = ⊔-lub (boundedDepth first) (objectBound rest)

record Bounded (allowance : ℕ) : Set where
  constructor bounded
  field tree : Tree; admitted : Within allowance tree

project : ∀ {allowance} → List (Bounded allowance) → List Tree
project = map Bounded.tree

projectProof : ∀ {allowance} values → All (Within allowance) (project values)
projectProof [] = All.[]
projectProof (value ∷ rest) = Bounded.admitted value All.∷ projectProof rest

projectMembers : ∀ {allowance} → List (String.StringValue × Bounded allowance) → List (String.StringValue × Tree)
projectMembers [] = []
projectMembers ((key , value) ∷ rest) = (key , Bounded.tree value) ∷ projectMembers rest

projectMemberProof : ∀ {allowance} members → All (λ member → Within allowance (proj₂ member)) (projectMembers members)
projectMemberProof [] = All.[]
projectMemberProof ((key , value) ∷ rest) = Bounded.admitted value All.∷ projectMemberProof rest

arrayValue : ∀ {allowance} → List (Bounded allowance) → Bounded (suc allowance)
arrayValue values = bounded (array (project values)) (array (projectProof values))

objectValue : ∀ {allowance} → List (String.StringValue × Bounded allowance) → Bounded (suc allowance)
objectValue members = bounded (object (projectMembers members)) (object (projectMemberProof members))

numericValue : ∀ {allowance} → Numeric.Number → Bounded allowance
numericValue (Numeric.unsigned64 value) = bounded (number (unsigned value)) number
numericValue (Numeric.signed64 value) = bounded (number (signed value)) number
numericValue (Numeric.binary64 (A.finite sign amount)) = bounded (number (floating sign amount)) number
numericValue (Numeric.binary64 (A.infinity sign)) = bounded null null
numericValue (Numeric.binary64 A.nan) = bounded null null
