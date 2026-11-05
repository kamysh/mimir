{-# OPTIONS --safe #-}
-- Rust's short-offset Unicode tables, with a total reference lookup and
-- constructive certificates for the source's unchecked-index premises.
module Mimir.UnicodeSkipSearch where

open import Data.Bool using (Bool; true; false)
import Data.Empty
open import Data.List using (List; []; _∷_; length; take; drop)
open import Data.List.Relation.Unary.All using (All; []; _∷_; all?)
open import Data.List.Relation.Unary.Any using (Any; here; there; any?)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; _<?_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-<-trans; n≤1+n; +-suc; <-trans)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable.Core using (_×-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
import Mimir.UpperBoundary as Upper

Header = ℕ × ℕ
start : Header → ℕ
start = proj₁
endpoint : Header → ℕ
endpoint = proj₂
module Boundary = Upper.Search Header endpoint

data Increasing : List Header → Set where
  empty : Increasing []
  singleton : ∀ entry → Increasing (entry ∷ [])
  next : ∀ {first second rest} → start first < start second → endpoint first < endpoint second →
    Increasing (second ∷ rest) → Increasing (first ∷ second ∷ rest)

increasingFrom? : ∀ first rest → Dec (Increasing (first ∷ rest))
increasingFrom? entry [] = yes (singleton entry)
increasingFrom? first (second ∷ rest) with start first <? start second | endpoint first <? endpoint second
... | no notIncreasing | _ = no (λ { (next startLess endLess tail) → notIncreasing startLess })
... | yes startLess | no notIncreasing = no (λ { (next startLess endLess tail) → notIncreasing endLess })
... | yes startLess | yes endLess with increasingFrom? second rest
...   | yes tail = yes (next startLess endLess tail)
...   | no badTail = no (λ { (next a b tail) → badTail tail })

increasing? : ∀ headers → Dec (Increasing headers)
increasing? [] = yes empty
increasing? (first ∷ rest) = increasingFrom? first rest

HeaderBounds : List ℕ → Header → Set
HeaderBounds offsets entry = start entry < length offsets × start entry < 2048 × endpoint entry < 2097152

headerBounds? : ∀ offsets entry → Dec (HeaderBounds offsets entry)
headerBounds? offsets entry = (start entry <? length offsets) ×-dec (start entry <? 2048) ×-dec (endpoint entry <? 2097152)

record Certified (headers : List Header) (offsets : List ℕ) : Set where
  constructor certified
  field
    byteOffsets : All (_< 256) offsets
    headerBounds : All (HeaderBounds offsets) headers
    increasing : Increasing headers
    sentinel : Any (λ entry → 1114111 < endpoint entry) headers

coveredBelow : ∀ {headers} needle → needle ≤ 1114111 →
  Any (λ entry → 1114111 < endpoint entry) headers → Any (λ entry → needle < endpoint entry) headers
coveredBelow needle bounded (here greater) = here (≤-<-trans bounded greater)
coveredBelow needle bounded (there later) = there (coveredBelow needle bounded later)

selectedBounds : ∀ {needle headers before entry after offsets} →
  Boundary.Boundary needle headers before entry after → All (HeaderBounds offsets) headers → HeaderBounds offsets entry
selectedBounds (Boundary.first greater) (bounded ∷ rest) = bounded
selectedBounds {offsets = offsets} (Boundary.skip lower proof) (bounded ∷ rest) = selectedBounds {offsets = offsets} proof rest

previous : ℕ → List Header → ℕ
previous fallback [] = fallback
previous fallback (entry ∷ rest) = previous (endpoint entry) rest

previousBound : ∀ {needle} fallback headers → fallback ≤ needle →
  All (λ entry → endpoint entry ≤ needle) headers → previous fallback headers ≤ needle
previousBound fallback [] bounded [] = bounded
previousBound fallback (entry ∷ rest) bounded (lower ∷ proof) = previousBound (endpoint entry) rest lower proof

odd : ℕ → Bool
odd zero = false
odd (suc zero) = true
odd (suc (suc n)) = odd n

-- The loop consumes offsets whose cumulative sum does not exceed total.
-- Its last source-table offset is deliberately excluded by the caller.
walk : ℕ → ℕ → ℕ → List ℕ → ℕ
walk total index prefix [] = index
walk total index prefix (offset ∷ rest) with total <? prefix + offset
... | yes above = index
... | no below = walk total (suc index) (prefix + offset) rest

data Walk (total : ℕ) : ℕ → ℕ → List ℕ → ℕ → Set where
  exhausted : ∀ {index prefix} → Walk total index prefix [] index
  stops : ∀ {index prefix offset rest} → total < prefix + offset →
    Walk total index prefix (offset ∷ rest) index
  crosses : ∀ {index prefix offset rest result} → (total < prefix + offset → Data.Empty.⊥) →
    Walk total (suc index) (prefix + offset) rest result → Walk total index prefix (offset ∷ rest) result

walkSound : ∀ total index prefix offsets → Walk total index prefix offsets (walk total index prefix offsets)
walkSound total index prefix [] = exhausted
walkSound total index prefix (offset ∷ rest) with total <? prefix + offset
... | yes above = stops above
... | no below = crosses below (walkSound total (suc index) (prefix + offset) rest)

walkComplete : ∀ {total index prefix offsets result} → Walk total index prefix offsets result →
  walk total index prefix offsets ≡ result
walkComplete exhausted = refl
walkComplete {total} {prefix = prefix} (stops {offset = offset} above) with total <? prefix + offset
... | yes accepted = refl
... | no rejected = Data.Empty.⊥-elim (rejected above)
walkComplete {total} {prefix = prefix} (crosses {offset = offset} below rest) with total <? prefix + offset
... | yes rejected = Data.Empty.⊥-elim (below rejected)
... | no accepted = walkComplete rest

walkLower : ∀ {total index prefix offsets result} → Walk total index prefix offsets result → index ≤ result
walkLower exhausted = ≤-refl
walkLower (stops above) = ≤-refl
walkLower (crosses {index = index} below rest) = ≤-trans (n≤1+n index) (walkLower rest)

walkUpper : ∀ {total index prefix offsets result} → Walk total index prefix offsets result → result ≤ index + length offsets
walkUpper {index = index} exhausted = subst (index ≤_) (sym (Data.Nat.Properties.+-identityʳ index)) ≤-refl
walkUpper {index = index} (stops {rest = rest} above) = Data.Nat.Properties.m≤m+n index (suc (length rest))
walkUpper {index = index} {result = result} (crosses {rest = rest} below proof) =
  subst (result ≤_) (sym (+-suc index (length rest))) (walkUpper proof)

endIndex : List ℕ → List Header → ℕ
endIndex offsets [] = length offsets
endIndex offsets (entry ∷ rest) = start entry

lookup : ℕ → List Header → List ℕ → Bool
lookup needle headers offsets with Boundary.search needle headers
... | Boundary.absent missing = false
... | Boundary.selected before entry after proof =
  odd (walk (needle ∸ previous 0 before) (start entry) 0
    (take (endIndex offsets after ∸ start entry ∸ 1) (drop (start entry) offsets)))

-- Certified tables always select an in-range header, and subtraction of the
-- previous cumulative endpoint cannot underflow for any Unicode scalar.
record Selection (needle : ℕ) (headers : List Header) (offsets : List ℕ) : Set where
  constructor selection
  field
    chosen : Boundary.Covered needle headers
    indexBound : length (Boundary.Covered.before chosen) < length headers
    offsetBound : start (Boundary.Covered.entry chosen) < length offsets
    previousBounded : previous 0 (Boundary.Covered.before chosen) ≤ needle

select : ∀ needle headers offsets → needle ≤ 1114111 → Certified headers offsets → Selection needle headers offsets
select needle headers offsets bounded valid with Boundary.selectCovered needle headers (coveredBelow needle bounded (Certified.sentinel valid))
... | chosen@(Boundary.covered before entry after proof) = selection chosen
  (Boundary.indexBound proof) (proj₁ (selectedBounds {offsets = offsets} proof (Certified.headerBounds valid)))
  (previousBound 0 before z≤n (Boundary.priorLower proof))
