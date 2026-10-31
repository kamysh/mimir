{-# OPTIONS --safe #-}
-- Canonical ordered object storage: replacement preserves one key, lookup
-- sees the last occurrence, and iteration remains strictly ordered.
module Mimir.OrderedObject where

open import Data.List using (List; []; _∷_; _++_)
import Data.List.Properties as List
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
open import Data.Nat using (_≟_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans)
import Mimir.ByteKeyOrder as Key

_≟Key_ = List.≡-dec _≟_

module Object (Value : Set) where
  Fields = List (Key.Key × Value)

  lookup : Key.Key → Fields → Maybe Value
  lookup key [] = nothing
  lookup key ((first , value) ∷ rest) with key ≟Key first
  ... | yes same = just value
  ... | no different = lookup key rest

  insert : Key.Key → Value → Fields → Fields
  insert key value [] = (key , value) ∷ []
  insert key value fields@((first , old) ∷ rest) with Key.compare key first
  ... | tri< before different notAfter = (key , value) ∷ fields
  ... | tri≈ notBefore same notAfter = (key , value) ∷ rest
  ... | tri> notBefore different after = (first , old) ∷ insert key value rest

  LowerBound : Key.Key → Fields → Set
  LowerBound key fields = All (λ entry → key Key.< proj₁ entry) fields

  data Sorted : Fields → Set where
    empty : Sorted []
    cons : ∀ {key value rest} → LowerBound key rest → Sorted rest → Sorted ((key , value) ∷ rest)

  strengthenLower : ∀ {first second fields} → first Key.< second → LowerBound second fields → LowerBound first fields
  strengthenLower before All.[] = All.[]
  strengthenLower before (orderedHead All.∷ rest) = Key.trans before orderedHead All.∷ strengthenLower before rest

  insertLower : ∀ lower key value fields → lower Key.< key → LowerBound lower fields → LowerBound lower (insert key value fields)
  insertLower lower key value [] before All.[] = before All.∷ All.[]
  insertLower lower key value fields@((first , old) ∷ rest) before (head All.∷ tail) with Key.compare key first
  ... | tri< earlier different notAfter = before All.∷ head All.∷ tail
  ... | tri≈ notBefore same notAfter = before All.∷ tail
  ... | tri> notBefore different later = head All.∷ insertLower lower key value rest before tail

  insertSorted : ∀ key value fields → Sorted fields → Sorted (insert key value fields)
  insertSorted key value [] empty = cons All.[] empty
  insertSorted key value fields@((first , old) ∷ rest) sorted@(cons lower tail) with Key.compare key first
  ... | tri< before different notAfter = cons (before All.∷ strengthenLower before lower) sorted
  ... | tri≈ notBefore refl notAfter = cons lower tail
  ... | tri> notBefore different after = cons (insertLower first key value rest after lower) (insertSorted key value rest tail)

  insertAll : ∀ {Predicate : Key.Key × Value → Set} key value fields →
    Predicate (key , value) → All Predicate fields → All Predicate (insert key value fields)
  insertAll key value [] admitted All.[] = admitted All.∷ All.[]
  insertAll key value fields@((first , old) ∷ rest) admitted (head All.∷ tail) with Key.compare key first
  ... | tri< before different notAfter = admitted All.∷ head All.∷ tail
  ... | tri≈ notBefore same notAfter = admitted All.∷ tail
  ... | tri> notBefore different after = head All.∷ insertAll key value rest admitted tail

  headLookup : ∀ key value rest → lookup key ((key , value) ∷ rest) ≡ just value
  headLookup key value rest with key ≟Key key
  ... | yes same = refl
  ... | no impossible = ⊥-elim (impossible refl)

  skipLookup : ∀ key first value rest → key ≢ first → lookup key ((first , value) ∷ rest) ≡ lookup key rest
  skipLookup key first value rest different with key ≟Key first
  ... | yes same = ⊥-elim (different same)
  ... | no other = refl

  insertedLookup : ∀ key value fields → lookup key (insert key value fields) ≡ just value
  insertedLookup key value [] = headLookup key value []
  insertedLookup key value fields@((first , old) ∷ rest) with Key.compare key first
  ... | tri< before different notAfter = headLookup key value fields
  ... | tri≈ notBefore same notAfter = headLookup key value rest
  ... | tri> notBefore different after = trans (skipLookup key first old (insert key value rest) different) (insertedLookup key value rest)

  otherLookup : ∀ key queried value fields → queried ≢ key → lookup queried (insert key value fields) ≡ lookup queried fields
  otherLookup key queried value [] different = skipLookup queried key value [] different
  otherLookup key queried value fields@((first , old) ∷ rest) different with Key.compare key first
  ... | tri< before unequal notAfter = skipLookup queried key value fields different
  ... | tri≈ notBefore refl notAfter = trans (skipLookup queried key value rest different)
      (Relation.Binary.PropositionalEquality.sym (skipLookup queried key old rest different))
  ... | tri> notBefore unequal after with queried ≟Key first
  ...   | yes same = refl
  ...   | no other = otherLookup key queried value rest different

  load : Fields → Fields → Fields
  load [] before = before
  load ((key , value) ∷ rest) before = load rest (insert key value before)

  loadSorted : ∀ fields before → Sorted before → Sorted (load fields before)
  loadSorted [] before sorted = sorted
  loadSorted ((key , value) ∷ rest) before sorted = loadSorted rest (insert key value before) (insertSorted key value before sorted)

  loadAll : ∀ {Predicate : Key.Key × Value → Set} fields before →
    All Predicate fields → All Predicate before → All Predicate (load fields before)
  loadAll [] before All.[] admitted = admitted
  loadAll ((key , value) ∷ rest) before (head All.∷ tail) admitted =
    loadAll rest (insert key value before) tail (insertAll key value before head admitted)

  loadAppend : ∀ first second before → load (first ++ second) before ≡ load second (load first before)
  loadAppend [] second before = refl
  loadAppend ((key , value) ∷ rest) second before = loadAppend rest second (insert key value before)

  normalize : Fields → Fields
  normalize fields = load fields []

  normalizedSorted : ∀ fields → Sorted (normalize fields)
  normalizedSorted fields = loadSorted fields [] empty

  lastOccurrenceWins : ∀ prefix key value → lookup key (normalize (prefix ++ ((key , value) ∷ []))) ≡ just value
  lastOccurrenceWins prefix key value = trans
    (cong (lookup key) (loadAppend prefix ((key , value) ∷ []) [])) (insertedLookup key value (normalize prefix))
