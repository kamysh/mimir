{-# OPTIONS --safe #-}
-- Bounds for every source-table loop access and cumulative offset addition.
module Mimir.UnicodeSkipBounds where

open import Data.List using (List; []; _∷_; length; take; drop)
open import Data.Nat.ListAction using (sum)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; _<?_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <⇒≤; ≤-<-trans; <-≤-trans;
  +-monoʳ-≤; +-assoc; m≤m+n; m≤n+m)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Mimir.UnicodeSkipSearch

selectedIncreasing : ∀ {needle headers before entry after} →
  Boundary.Boundary needle headers before entry after → Increasing headers → Increasing (entry ∷ after)
selectedIncreasing (Boundary.first greater) ordered = ordered
selectedIncreasing (Boundary.skip lower proof) (next startLess endLess ordered) = selectedIncreasing proof ordered

selectedTailBounds : ∀ {needle headers before entry after offsets} →
  Boundary.Boundary needle headers before entry after → All (HeaderBounds offsets) headers →
  All (HeaderBounds offsets) (entry ∷ after)
selectedTailBounds (Boundary.first greater) bounded = bounded
selectedTailBounds {offsets = offsets} (Boundary.skip lower proof) (bounded ∷ rest) =
  selectedTailBounds {offsets = offsets} proof rest

positiveRun : ∀ offsets entry after → Increasing (entry ∷ after) →
  All (HeaderBounds offsets) (entry ∷ after) → start entry < endIndex offsets after
positiveRun offsets entry [] (singleton _) (bounded ∷ []) = proj₁ bounded
positiveRun offsets entry (second ∷ rest) (next startLess endLess ordered) bounded = startLess

endBound : ∀ offsets entry after → All (HeaderBounds offsets) (entry ∷ after) →
  endIndex offsets after ≤ length offsets
endBound offsets entry [] bounded = ≤-refl
endBound offsets entry (second ∷ rest) (bounded ∷ nextBound ∷ tail) = <⇒≤ (proj₁ nextBound)

lastIndexBelowEnd : ∀ start end → start < end → start + (end ∸ start ∸ 1) < end
lastIndexBelowEnd zero (suc end) bounded = s≤s ≤-refl
lastIndexBelowEnd (suc start) (suc end) (s≤s bounded) = s≤s (lastIndexBelowEnd start end bounded)

takeLengthBound : ∀ {A : Set} count (input : List A) → length (take count input) ≤ count
takeLengthBound zero input = z≤n
takeLengthBound (suc count) [] = z≤n
takeLengthBound (suc count) (entry ∷ rest) = s≤s (takeLengthBound count rest)

runBounds : ∀ {needle headers before entry after} offsets →
  Boundary.Boundary needle headers before entry after → Certified headers offsets →
  start entry < endIndex offsets after ×
  start entry + (endIndex offsets after ∸ start entry ∸ 1) < length offsets
runBounds {entry = entry} {after = after} offsets proof valid = positive ,
  <-≤-trans (lastIndexBelowEnd (start entry) (endIndex offsets after) positive)
    (endBound offsets entry after bounded)
  where
  bounded = selectedTailBounds {offsets = offsets} proof (Certified.headerBounds valid)
  positive = positiveRun offsets entry after (selectedIncreasing proof (Certified.increasing valid)) bounded

lookupIndexBound : ∀ {needle headers before entry after} offsets →
  Boundary.Boundary needle headers before entry after → Certified headers offsets →
  walk (needle ∸ previous 0 before) (start entry) 0
    (take (endIndex offsets after ∸ start entry ∸ 1) (drop (start entry) offsets)) < length offsets
lookupIndexBound {needle} {before = before} {entry} {after} offsets proof valid =
  ≤-<-trans (≤-trans (walkUpper (walkSound (needle ∸ previous 0 before) (start entry) 0
      (take count (drop (start entry) offsets))))
    (+-monoʳ-≤ (start entry) (takeLengthBound count (drop (start entry) offsets))))
    (Data.Product.proj₂ (runBounds offsets proof valid))
  where count = endIndex offsets after ∸ start entry ∸ 1

sumTakeBound : ∀ count input → sum (take count input) ≤ sum input
sumTakeBound zero input = z≤n
sumTakeBound (suc count) [] = z≤n
sumTakeBound (suc count) (entry ∷ rest) = +-monoʳ-≤ entry (sumTakeBound count rest)

sumDropBound : ∀ count input → sum (drop count input) ≤ sum input
sumDropBound zero input = ≤-refl
sumDropBound (suc count) [] = z≤n
sumDropBound (suc count) (entry ∷ rest) = ≤-trans (sumDropBound count rest) (m≤n+m (sum rest) entry)

sumSliceBound : ∀ count begin input → sum (take count (drop begin input)) ≤ sum input
sumSliceBound count begin input = ≤-trans (sumTakeBound count (drop begin input)) (sumDropBound begin input)

-- Includes the addition made before a stopping comparison, not just the
-- sums of offsets that the loop subsequently accepts.
updates : ℕ → ℕ → List ℕ → List ℕ
updates total prefix [] = []
updates total prefix (offset ∷ rest) with total <? prefix + offset
... | yes above = (prefix + offset) ∷ []
... | no below = (prefix + offset) ∷ updates total (prefix + offset) rest

raiseAll : ∀ {low high input} → low ≤ high → All (_≤ low) input → All (_≤ high) input
raiseAll bounded [] = []
raiseAll bounded (lower ∷ rest) = ≤-trans lower bounded ∷ raiseAll bounded rest

updatesBound : ∀ total prefix input → All (_≤ (prefix + sum input)) (updates total prefix input)
updatesBound total prefix [] = []
updatesBound total prefix (offset ∷ rest) with total <? prefix + offset
... | yes above = subst ((prefix + offset) ≤_) (+-assoc prefix offset (sum rest))
  (m≤m+n (prefix + offset) (sum rest)) ∷ []
... | no below = subst ((prefix + offset) ≤_) (+-assoc prefix offset (sum rest))
  (m≤m+n (prefix + offset) (sum rest)) ∷
  subst (λ bound → All (_≤ bound) (updates total (prefix + offset) rest))
    (+-assoc prefix offset (sum rest)) (updatesBound total (prefix + offset) rest)

updatesBelow : ∀ limit total count begin input → sum input < limit →
  All (_< limit) (updates total 0 (take count (drop begin input)))
updatesBelow limit total count begin input bounded = tighten
  (raiseAll (sumSliceBound count begin input) (updatesBound total 0 (take count (drop begin input))))
  where
  tighten : ∀ {values} → All (_≤ sum input) values → All (_< limit) values
  tighten [] = []
  tighten (lower ∷ rest) = ≤-<-trans lower bounded ∷ tighten rest
