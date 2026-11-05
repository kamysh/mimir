{-# OPTIONS --safe #-}
-- Universal chain, prefix and termination bounds for byte-preserving parents.
module Mimir.UnixPathAncestry where

open import Data.List using (List; []; _∷_; _++_; length; take; drop)
open import Data.List.Properties using (take++drop≡id)
open import Data.Maybe using (nothing; just)
open import Data.Fin using (toℕ)
open import Data.Nat using (suc; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Induction.WellFounded using (Acc; acc)
open import Mimir.UnixPath using (Path)
open import Mimir.UnixPathParent

parentPrefix : ∀ path shorter bound → parent path ≡ just (shorter , bound) →
  Σ Path (λ removed → path ≡ shorter ++ removed)
parentPrefix path shorter bound receipt with Cursor.previous (scanPath path)
... | nothing with receipt
...   | ()
parentPrefix path shorter bound receipt | just index with receipt
... | refl = drop (toℕ index) path , sym (take++drop≡id (toℕ index) path)

data Chain : Path → List Path → Set where
  last : ∀ {path} → parent path ≡ nothing → Chain path (path ∷ [])
  step : ∀ {path shorter rest} (bound : length shorter < length path) →
    parent path ≡ just (shorter , bound) → Chain shorter rest → Chain path (path ∷ rest)

walkChain : ∀ path accessibility → Chain path (walk path accessibility)
walkChain path (acc below) with parent path in observed
... | nothing = last observed
... | just (shorter , bound) = step bound observed (walkChain shorter (below bound))

ancestryChain : ∀ path → Chain path (ancestors path)
ancestryChain path = walkChain path (<-wellFounded (length path))

chainBound : ∀ {path paths} → Chain path paths → length paths ≤ suc (length path)
chainBound (last _) = s≤s z≤n
chainBound (step bound _ rest) = s≤s (≤-trans (chainBound rest) bound)

ancestryBound : ∀ path → length (ancestors path) ≤ suc (length path)
ancestryBound path = chainBound (ancestryChain path)

-- The well-founded termination witness cannot change the returned paths.
walkIndependent : ∀ path first second → walk path first ≡ walk path second
walkIndependent path (acc first) (acc second) with parent path
... | nothing = refl
... | just (shorter , bound) = cong (path ∷_) (walkIndependent shorter (first bound) (second bound))
