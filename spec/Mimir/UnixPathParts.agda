{-# OPTIONS --safe #-}
-- Independent lexical meaning of path components and its agreement with the
-- byte classifier. A normal component cannot hide an exact '.' or '..'.
module Mimir.UnixPathParts where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Fin using (_≟_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Mimir.UnixPath

Clean : Path → Set
Clean = All (λ byte → byte ≢ slash)

Separated : Chunks → Set
Separated groups = All Clean (chunkList groups)

prependClean : ∀ byte groups → byte ≢ slash → Separated groups → Separated (prepend byte groups)
prependClean byte (chunks first rest) ordinary (firstClean ∷ restClean) = (ordinary ∷ firstClean) ∷ restClean

separateClean : ∀ groups → Separated groups → Separated (separate groups)
separateClean (chunks first rest) clean = [] ∷ clean

splitClean : ∀ path → Separated (split path)
splitClean [] = [] ∷ []
splitClean (byte ∷ rest) with byte ≟ slash
... | yes _ = separateClean (split rest) (splitClean rest)
... | no ordinary = prependClean byte (split rest) ordinary (splitClean rest)

data Meaning : Path → Maybe Component → Set where
  empty : Meaning [] nothing
  dotOnly : Meaning (dot ∷ []) nothing
  parent : Meaning (dot ∷ dot ∷ []) (just parentDir)
  ordinary : ∀ {path} → path ≢ [] → path ≢ (dot ∷ []) → path ≢ (dot ∷ dot ∷ []) →
    Meaning path (just (normal path))

partSound : ∀ path → Meaning path (part path)
partSound [] = empty
partSound (byte ∷ []) with byte ≟ dot
... | yes refl = dotOnly
... | no notDot = ordinary (λ ()) (λ { refl → notDot refl }) (λ ())
partSound (first ∷ second ∷ []) with first ≟ dot | second ≟ dot
... | yes refl | yes refl = parent
... | yes refl | no notDot = ordinary (λ ()) (λ ()) (λ { refl → notDot refl })
... | no notDot | _ = ordinary (λ ()) (λ ()) (λ { refl → notDot refl })
partSound (first ∷ second ∷ third ∷ rest) = ordinary (λ ()) (λ ()) (λ ())

meaningUnique : ∀ {path first second} → Meaning path first → Meaning path second → first ≡ second
meaningUnique empty empty = refl
meaningUnique empty (ordinary nonempty _ _) = ⊥-elim (nonempty refl)
meaningUnique dotOnly dotOnly = refl
meaningUnique dotOnly (ordinary _ notDot _) = ⊥-elim (notDot refl)
meaningUnique parent parent = refl
meaningUnique parent (ordinary _ _ notParent) = ⊥-elim (notParent refl)
meaningUnique (ordinary nonempty _ _) empty = ⊥-elim (nonempty refl)
meaningUnique (ordinary _ notDot _) dotOnly = ⊥-elim (notDot refl)
meaningUnique (ordinary _ _ notParent) parent = ⊥-elim (notParent refl)
meaningUnique (ordinary _ _ _) (ordinary _ _ _) = refl

partComplete : ∀ path expected → Meaning path expected → part path ≡ expected
partComplete path expected meaning = meaningUnique (partSound path) meaning

data NotParent : Component → Set where
  root : NotParent rootDir
  current : NotParent curDir
  ordinary : ∀ path → NotParent (normal path)

notParent? : ∀ component → Dec (NotParent component)
notParent? rootDir = yes root
notParent? curDir = yes current
notParent? parentDir = no (λ ())
notParent? (normal path) = yes (ordinary path)

NoParent : Path → Set
NoParent path = All NotParent (components path)

allNotParent? : ∀ parts → Dec (All NotParent parts)
allNotParent? [] = yes []
allNotParent? (component ∷ parts) with notParent? component
... | no rejected = no (λ { (head ∷ _) → rejected head })
... | yes head with allNotParent? parts
...   | no rejected = no (λ { (_ ∷ tail) → rejected tail })
...   | yes tail = yes (head ∷ tail)

noParent? : ∀ path → Dec (NoParent path)
noParent? path = allNotParent? (components path)
