{-# OPTIONS --safe #-}
module Mimir.UnixPathLaws where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_; _++_)
open import Data.Fin using (_≟_)
open import Data.Product using (Σ; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Mimir.UnixPath

Absolute : Path → Set
Absolute path = absolute path ≡ true

rootAbsolute : ∀ rest → Absolute (slash ∷ rest)
rootAbsolute rest with slash ≟ slash
... | yes _ = refl
... | no different = ⊥-elim (different refl)

absolutePrefix : ∀ path → Absolute path → Σ Path (λ rest → path ≡ slash ∷ rest)
absolutePrefix [] ()
absolutePrefix (byte ∷ rest) proof with byte ≟ slash
... | yes refl = rest , refl
... | no _ with proof
...   | ()

appendAbsolute : ∀ base suffix → Absolute base → Absolute (base ++ suffix)
appendAbsolute base suffix isAbsolute with absolutePrefix base isAbsolute
... | rest , refl = rootAbsolute (rest ++ suffix)

relativeJoinAbsolute : ∀ base suffix → Absolute base → Absolute (joinRelative base suffix)
relativeJoinAbsolute base suffix isAbsolute with needsSeparator base
... | true = appendAbsolute base (slash ∷ suffix) isAbsolute
... | false = appendAbsolute base suffix isAbsolute

joinAbsolute : ∀ base suffix → Absolute base → Absolute (join base suffix)
joinAbsolute base suffix isAbsolute with absolute suffix in observed
... | true = observed
... | false = relativeJoinAbsolute base suffix isAbsolute

absoluteReplaces : ∀ base suffix → Absolute suffix → join base suffix ≡ suffix
absoluteReplaces base suffix isAbsolute with absolute suffix
... | true = refl
... | false with isAbsolute
...   | ()
