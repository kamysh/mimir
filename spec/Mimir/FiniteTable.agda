{-# OPTIONS --safe #-}
-- Finite keyed state with extensional laws. A finite support witness prevents
-- an arbitrary infinite function from standing in for a stored table. Equality
-- of tables is pointwise; function extensionality is not postulated.
module Mimir.FiniteTable where

open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym)

module Tables (Key Value : Set) (equal : DecidableEquality Key) where
  record Table : Set where
    constructor table
    field
      lookup : Key → Maybe Value
      support : List Key
      finite : ∀ key → ¬ (key ∈ support) → lookup key ≡ nothing
  open Table public

  empty : Table
  empty = table (λ _ → nothing) [] (λ _ _ → refl)

  assign : Key → Value → Table → Key → Maybe Value
  assign key value old query with equal query key
  ... | yes _ = just value
  ... | no _ = lookup old query

  assignFinite : ∀ key value old query → ¬ (query ∈ key ∷ support old) →
    assign key value old query ≡ nothing
  assignFinite key value old query absent with equal query key
  ... | yes same = ⊥-elim (absent (here same))
  ... | no _ = finite old query (λ found → absent (there found))

  put : Key → Value → Table → Table
  put key value old = table (assign key value old) (key ∷ support old) (assignFinite key value old)

  erase : Key → Table → Key → Maybe Value
  erase key old query with equal query key
  ... | yes _ = nothing
  ... | no _ = lookup old query

  eraseFinite : ∀ key old query → ¬ (query ∈ support old) → erase key old query ≡ nothing
  eraseFinite key old query absent with equal query key
  ... | yes _ = refl
  ... | no _ = finite old query absent

  remove : Key → Table → Table
  remove key old = table (erase key old) (support old) (eraseFinite key old)

  insertAbsent : Key → Value → Table → Table
  insertAbsent key value old with lookup old key
  ... | nothing = put key value old
  ... | just previous = old

  Equivalent : Table → Table → Set
  Equivalent left right = ∀ query → lookup left query ≡ lookup right query

  putSame : ∀ key value old → lookup (put key value old) key ≡ just value
  putSame key value old with equal key key
  ... | yes _ = refl
  ... | no impossible = ⊥-elim (impossible refl)

  putOther : ∀ key value old query → query ≢ key →
    lookup (put key value old) query ≡ lookup old query
  putOther key value old query different with equal query key
  ... | yes same = ⊥-elim (different same)
  ... | no _ = refl

  Contains : Table → Key → Set
  Contains state query = Σ Value λ value → lookup state query ≡ just value

  putDomain : ∀ key value old query → Contains (put key value old) query →
    query ≡ key ⊎ Contains old query
  putDomain key value old query (stored , found) with equal query key
  ... | yes same = inj₁ same
  ... | no different = inj₂ (stored , found)

  putDomainBack : ∀ key value old query → query ≡ key ⊎ Contains old query →
    Contains (put key value old) query
  putDomainBack key value old query (inj₁ refl) = value , putSame key value old
  putDomainBack key value old query (inj₂ (stored , found)) with equal query key
  ... | yes refl = value , refl
  ... | no different = stored , found

  removeSame : ∀ key old → lookup (remove key old) key ≡ nothing
  removeSame key old with equal key key
  ... | yes _ = refl
  ... | no impossible = ⊥-elim (impossible refl)

  removeOther : ∀ key old query → query ≢ key →
    lookup (remove key old) query ≡ lookup old query
  removeOther key old query different with equal query key
  ... | yes same = ⊥-elim (different same)
  ... | no _ = refl

  putIdempotent : ∀ key value old → Equivalent (put key value (put key value old)) (put key value old)
  putIdempotent key value old query with equal query key
  ... | yes _ = refl
  ... | no different = putOther key value old query different

  putLastWins : ∀ key previous current old →
    Equivalent (put key current (put key previous old)) (put key current old)
  putLastWins key previous current old query with equal query key
  ... | yes _ = refl
  ... | no different = putOther key previous old query different

  removeIdempotent : ∀ key old → Equivalent (remove key (remove key old)) (remove key old)
  removeIdempotent key old query with equal query key
  ... | yes _ = refl
  ... | no different = removeOther key old query different

  insertPreservesPresent : ∀ key value old previous → lookup old key ≡ just previous →
    insertAbsent key value old ≡ old
  insertPreservesPresent key value old previous found rewrite found = refl

  insertAtAbsent : ∀ key value old → lookup old key ≡ nothing →
    lookup (insertAbsent key value old) key ≡ just value
  insertAtAbsent key value old absent rewrite absent = putSame key value old

  insertOther : ∀ key value old query → query ≢ key →
    lookup (insertAbsent key value old) query ≡ lookup old query
  insertOther key value old query different with lookup old key
  ... | just previous = refl
  ... | nothing = putOther key value old query different

  insertRetainsLookup : ∀ key value old query previous → lookup old query ≡ just previous →
    lookup (insertAbsent key value old) query ≡ just previous
  insertRetainsLookup key value old query previous found with equal query key
  ... | yes refl rewrite insertPreservesPresent key value old previous found = found
  ... | no different = trans (insertOther key value old query different) found

  insertSome : ∀ key value old → Σ Value λ stored → lookup (insertAbsent key value old) key ≡ just stored
  insertSome key value old with lookup old key in found
  ... | nothing = value , putSame key value old
  ... | just previous = previous , found

  insertIdempotent : ∀ key value old →
    Equivalent (insertAbsent key value (insertAbsent key value old)) (insertAbsent key value old)
  insertIdempotent key value old query with lookup old key in found
  ... | just previous rewrite insertPreservesPresent key value old previous found = refl
  ... | nothing rewrite putSame key value old = refl
