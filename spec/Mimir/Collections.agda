{-# OPTIONS --safe #-}
-- Decidable finite collections with evidence independent of the validator.
module Mimir.Collections where

import Data.Empty

open import Data.List using (List; []; _∷_; length; take)
open import Data.Bool using (Bool; true)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Nat using (ℕ; _≤_; _≤?_)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no; ¬_; does)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Mimir.Validation

limitResults : ∀ {A : Set} → Maybe ℕ → List A → List A
limitResults nothing values = values
limitResults (just count) values = take count values

validSelection : Maybe ℕ → Bool
validSelection nothing = true
validSelection (just count) = does (1 ≤? count)

atMost : ∀ {A : Set} → ℕ → List A → Set
atMost maximum values = length values ≤ maximum

checkCount : ∀ {A : Set} maximum (values : List A) → Checked (atMost maximum values)
checkCount maximum values = check (fault [] tooMany "collection exceeds its size limit")
  (length values ≤? maximum)

withinSelection : ∀ {A : Set} → Maybe ℕ → List A → Set
withinSelection nothing values = ⊤
withinSelection (just maximum) values = atMost maximum values

checkSelection : ∀ {A : Set} selection (values : List A) → Checked (withinSelection selection values)
checkSelection nothing values = check (fault [] tooMany "collection exceeds the requested count") (yes tt)
checkSelection (just maximum) values = checkCount maximum values

all? : ∀ {A : Set} {P : A → Set} → ((x : A) → Dec (P x)) → (xs : List A) → Dec (All P xs)
all? p [] = yes []
all? p (x ∷ xs) with p x | all? p xs
... | yes px | yes ps = yes (px ∷ ps)
... | no notP | _ = no (λ { (px ∷ ps) → notP px })
... | _ | no notPs = no (λ { (px ∷ ps) → notPs ps })

any? : ∀ {A : Set} {P : A → Set} → ((x : A) → Dec (P x)) → (xs : List A) → Dec (Any P xs)
any? p [] = no (λ ())
any? p (x ∷ xs) with p x
... | yes px = yes (here px)
... | no notP with any? p xs
...   | yes ps = yes (there ps)
...   | no notPs = no (λ { (here px) → notP px ; (there ps) → notPs ps })

negate : ∀ {P : Set} → Dec P → Dec (¬ P)
negate (yes p) = no (λ notP → notP p)
negate (no notP) = yes notP

pairEqual : ∀ {A B : Set} → ((x y : A) → Dec (x ≡ y)) →
  ((x y : B) → Dec (x ≡ y)) → (x y : A × B) → Dec (x ≡ y)
pairEqual eqA eqB (a , b) (c , d) with eqA a c | eqB b d
... | yes refl | yes refl = yes refl
... | no different | _ = no (λ { refl → different refl })
... | _ | no different = no (λ { refl → different refl })

maybeEqual : ∀ {A : Set} → ((x y : A) → Dec (x ≡ y)) →
  (x y : Maybe A) → Dec (x ≡ y)
maybeEqual eq nothing nothing = yes refl
maybeEqual eq nothing (just y) = no (λ ())
maybeEqual eq (just x) nothing = no (λ ())
maybeEqual eq (just x) (just y) with eq x y
... | yes refl = yes refl
... | no different = no (λ { refl → different refl })

module Equality (A : Set) (_≟_ : (x y : A) → Dec (x ≡ y)) where
  Present : A → List A → Set
  Present x = Any (x ≡_)

  present? : ∀ x xs → Dec (Present x xs)
  present? x = any? (x ≟_)

  Absent : A → List A → Set
  Absent x = All (x ≢_)

  absent? : ∀ x xs → Dec (Absent x xs)
  absent? x = all? (λ y → negate (x ≟ y))

  Unique : List A → Set
  Unique [] = ⊤
  Unique (x ∷ xs) = Absent x xs × Unique xs

  unique? : ∀ xs → Dec (Unique xs)
  unique? [] = yes tt
  unique? (x ∷ xs) with absent? x xs | unique? xs
  ... | yes p | yes q = yes (p , q)
  ... | no notP | _ = no (λ { (p , q) → notP p })
  ... | _ | no notQ = no (λ { (p , q) → notQ q })

  checkUnique : ∀ xs → Checked (Unique xs)
  checkUnique xs = check (fault [] duplicate "duplicate collection key") (unique? xs)

  presentAbsentContradiction : ∀ {x xs} → Present x xs → Absent x xs → Data.Empty.⊥
  presentAbsentContradiction (here same) (different ∷ rest) = different same
  presentAbsentContradiction (there present) (different ∷ rest) = presentAbsentContradiction present rest
