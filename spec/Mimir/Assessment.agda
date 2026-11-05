{-# OPTIONS --safe #-}
module Mimir.Assessment where

open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; -_; _≤_)
open import Data.Rational.Properties using
  (≤-refl; ≤-trans; ≤-reflexive; +-mono-≤; +-identityˡ;
   +-identityʳ; neg-distrib-+; neg-antimono-≤; nonNegative⁻¹)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; _≟_)
open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong)
open import Mimir.Learning using (module Contributions)

-- Weighted contributions after validation. These are separate from graph priors.
record Mass : Set where
  constructor mass
  field positive negative benefit weight : ℚ
open Mass

record Bounded (m : Mass) : Set where
  constructor bounded
  field
    positive≥0 : 0ℚ ≤ positive m
    negative≥0 : 0ℚ ≤ negative m
    weight≥0 : 0ℚ ≤ weight m
    benefit-lower : - weight m ≤ benefit m
    benefit-upper : benefit m ≤ weight m
open Bounded

add : Mass → Mass → Mass
add a b = mass (positive a + positive b) (negative a + negative b)
              (benefit a + benefit b) (weight a + weight b)

-- Summing valid evidence preserves numerator bounds for both scores.
add-bounded : ∀ a b → Bounded a → Bounded b → Bounded (add a b)
add-bounded a b va vb = bounded
  (+-mono-≤ (positive≥0 va) (positive≥0 vb))
  (+-mono-≤ (negative≥0 va) (negative≥0 vb))
  (+-mono-≤ (weight≥0 va) (weight≥0 vb))
  (≤-trans (≤-reflexive (neg-distrib-+ (weight a) (weight b)))
    (+-mono-≤ (benefit-lower va) (benefit-lower vb)))
  (+-mono-≤ (benefit-upper va) (benefit-upper vb))

prior : Mass
prior = mass 1ℚ 1ℚ 0ℚ 1ℚ

prior-bounded : Bounded prior
prior-bounded = bounded (nonNegative⁻¹ 1ℚ) (nonNegative⁻¹ 1ℚ)
  (nonNegative⁻¹ 1ℚ) (neg-antimono-≤ (nonNegative⁻¹ 1ℚ)) (nonNegative⁻¹ 1ℚ)

total : List Mass → Mass
total [] = prior
total (x ∷ xs) = add x (total xs)

data Valid : List Mass → Set where
  empty : Valid []
  more : ∀ {x xs} → Bounded x → Valid xs → Valid (x ∷ xs)

total-bounded : ∀ {xs} → Valid xs → Bounded (total xs)
total-bounded empty = prior-bounded
total-bounded (more {x} {xs} vx vs) = add-bounded x (total xs) vx (total-bounded vs)

-- Exact cross-multiplied probability bound: A ≤ A+B, with nonnegative A.
correctness-upper : ∀ {xs} → Valid xs →
  positive (total xs) ≤ positive (total xs) + negative (total xs)
correctness-upper {xs} valid = ≤-trans
  (≤-reflexive (sym (+-identityʳ (positive (total xs)))))
  (+-mono-≤ (≤-refl {positive (total xs)}) (negative≥0 (total-bounded valid)))

usefulness-lower : ∀ {xs} → Valid xs → - weight (total xs) ≤ benefit (total xs)
usefulness-lower valid = benefit-lower (total-bounded valid)

usefulness-upper : ∀ {xs} → Valid xs → benefit (total xs) ≤ weight (total xs)
usefulness-upper valid = benefit-upper (total-bounded valid)

-- The neutral prior makes the usefulness denominator strictly positive.
denominator≥one : ∀ {xs} → Valid xs → 1ℚ ≤ weight (total xs)
denominator≥one empty = ≤-refl
denominator≥one (more {x} {xs} vx vs) = ≤-trans
  (≤-reflexive (sym (+-identityˡ 1ℚ)))
  (+-mono-≤ (weight≥0 vx) (denominator≥one vs))

correctness-numerator≥one : ∀ {xs} → Valid xs → 1ℚ ≤ positive (total xs)
correctness-numerator≥one empty = ≤-refl
correctness-numerator≥one (more vx vs) = ≤-trans
  (≤-reflexive (sym (+-identityˡ 1ℚ)))
  (+-mono-≤ (positive≥0 vx) (correctness-numerator≥one vs))

unknown : Mass
unknown = mass 0ℚ 0ℚ 0ℚ 0ℚ

unknown-inert : ∀ xs → total (unknown ∷ xs) ≡ total xs
unknown-inert xs rewrite +-identityˡ (positive (total xs))
  | +-identityˡ (negative (total xs)) | +-identityˡ (benefit (total xs))
  | +-identityˡ (weight (total xs)) = refl

module Ledger = Contributions Mass
assess : Ledger.Ledger → Mass
assess xs = total (map proj₂ xs)

retry-inert : ∀ id evidence xs →
  assess (Ledger.replace id evidence (Ledger.replace id evidence xs)) ≡
  assess (Ledger.replace id evidence xs)
retry-inert id evidence xs = cong assess (Ledger.replace-idempotent id evidence xs)

correction-forgets-old : ∀ id new old xs →
  assess (Ledger.replace id new (Ledger.replace id old xs)) ≡
  assess (Ledger.replace id new xs)
correction-forgets-old id new old xs = cong assess (Ledger.replacement-forgets-old id new old xs)

stale-review-has-prior : ∀ current reviewed evidence → current ≢ reviewed →
  total (Ledger.active current reviewed evidence) ≡ prior
stale-review-has-prior current reviewed evidence neq =
  cong total (Ledger.stale-review-contributes-nothing current reviewed evidence neq)

-- A group key encodes project, lesson, applicability scope and benefit rubric.
visible : ℕ → List (ℕ × Mass) → List Mass
visible group [] = []
visible group ((key , evidence) ∷ xs) with group ≟ key
... | yes _ = evidence ∷ visible group xs
... | no _ = visible group xs

unrelated-group-inert : ∀ group foreign evidence xs → group ≢ foreign →
  total (visible group ((foreign , evidence) ∷ xs)) ≡ total (visible group xs)
unrelated-group-inert group foreign evidence xs neq with group ≟ foreign
... | yes eq = ⊥-elim (neq eq)
... | no _ = refl

-- Neither evidence nor an assessment can mutate an arbitrary control state.
observe : ∀ {Control : Set} → Control → Ledger.Ledger → Control × Mass
observe control ledger = control , assess ledger
control-preserved : ∀ {Control : Set} (control : Control) ledger →
  proj₁ (observe control ledger) ≡ control
control-preserved control ledger = refl
