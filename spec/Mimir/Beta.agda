{-# OPTIONS --safe #-}
-- Phase 3 — beliefs as Beta(α, β).
--
-- A belief's evidence state is a Beta distribution with ℕ pseudo-counts α, β:
--   mean      = α / (α + β)   (the value the rest of the system reads as "probability")
--   strength  = α + β         (pseudo-count; what "confidence" was gesturing at)
--
-- The prior (α₀, β₀) is fixed at insertion; the posterior is recomputed as
-- (α₀ + Σ pos_evidence, β₀ + Σ neg_evidence) from the edge structure on each
-- propagation — so propagation is IDEMPOTENT (re-deriving evidence cannot drift),
-- which Phase 2 could not promise.
--
-- KEY MODELLING CHOICE: mean comparison is stated by CROSS-MULTIPLICATION
--   mean b₁ ≤ mean b₂  ⟺  α₁·(α₂+β₂) ≤ α₂·(α₁+β₁)
-- This is the exact rational order; it sidesteps the truncating ℕ division used
-- by `betaMean`, so the monotonicity proofs below are EXACT, not approximate.
module Mimir.Beta where

open import Mimir.Types using (Prob; mkProb)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _/_; _≤_; NonZero)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; *-comm; *-monoʳ-≤; +-monoʳ-≤; m≤m+n;
         +-assoc; +-comm)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver
open import Data.List using (List; []; _∷_)
import Data.List.Relation.Binary.Permutation.Propositional as P
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans)

-- ---------------------------------------------------------------------------
-- The Beta state
-- ---------------------------------------------------------------------------

record Beta : Set where
  constructor mkBeta
  field
    α : ℕ
    β : ℕ

open Beta

-- Pseudo-count strength α + β.
strength : Beta → ℕ
strength b = α b + β b

-- The mean as a Prob (percent), α·100 / (α+β).  Needs α+β ≠ 0; the instance is
-- supplied explicitly at concrete use sites (cf. the do-operator's /pow trick).
betaMean : (b : Beta) → .{{NonZero (strength b)}} → Prob
betaMean b = mkProb (α b * 100 / strength b)

-- Cross-multiplied "mean b₁ ≤ mean b₂": α₁·(α₂+β₂) ≤ α₂·(α₁+β₁).
mean≤ : Beta → Beta → Set
mean≤ b₁ b₂ = α b₁ * strength b₂ ≤ α b₂ * strength b₁

-- ---------------------------------------------------------------------------
-- (1) mean ∈ [0,1].  As a rational, α/(α+β) ≤ 1 ⟺ α ≤ α+β.
-- ---------------------------------------------------------------------------

mean-≤1 : ∀ (b : Beta) → α b ≤ strength b
mean-≤1 b = m≤m+n (α b) (β b)

-- ---------------------------------------------------------------------------
-- (2) Support increases α ⇒ mean does not decrease.
--   mean (α, β) ≤ mean (α + d, β).
-- ---------------------------------------------------------------------------

support-mono : ∀ (b : Beta) (d : ℕ) → mean≤ b (mkBeta (α b + d) (β b))
support-mono b d = goal
  where
    a = α b
    c = β b
    -- a·((a+d)+c) ≡ a·(a+c) + a·d
    eqL : a * ((a + d) + c) ≡ a * (a + c) + a * d
    eqL = solve 3 (λ a d c → a :* ((a :+ d) :+ c) := a :* (a :+ c) :+ a :* d)
                  refl a d c
    -- a·(a+c) + d·(a+c) ≡ (a+d)·(a+c)
    eqR : a * (a + c) + d * (a + c) ≡ (a + d) * (a + c)
    eqR = solve 3 (λ a d c → a :* (a :+ c) :+ d :* (a :+ c) := (a :+ d) :* (a :+ c))
                  refl a d c
    -- a·d ≤ d·(a+c)
    ad≤ : a * d ≤ d * (a + c)
    ad≤ = ≤-trans (≤-reflexive (*-comm a d)) (*-monoʳ-≤ d (m≤m+n a c))
    -- a·(a+c) + a·d ≤ a·(a+c) + d·(a+c)
    mid : a * (a + c) + a * d ≤ a * (a + c) + d * (a + c)
    mid = +-monoʳ-≤ (a * (a + c)) ad≤
    goal : a * ((a + d) + c) ≤ (a + d) * (a + c)
    goal = ≤-trans (≤-reflexive eqL) (≤-trans mid (≤-reflexive eqR))

-- ---------------------------------------------------------------------------
-- (3) Defeat increases β ⇒ mean does not increase.
--   mean (α, β + d) ≤ mean (α, β).
-- Clean: numerator α fixed, denominator grows, so the cross-product order is
-- just α·(α+β) ≤ α·(α+(β+d)).
-- ---------------------------------------------------------------------------

defeat-anti : ∀ (b : Beta) (d : ℕ) → mean≤ (mkBeta (α b) (β b + d)) b
defeat-anti b d = *-monoʳ-≤ (α b) (+-monoʳ-≤ (α b) (m≤m+n (β b) d))

-- ---------------------------------------------------------------------------
-- (4) Idempotence of conjugate recomputation.
-- The posterior is re-derived from the FIXED prior (α₀,β₀) plus the evidence
-- sums (pos,neg); it never reads the belief's current (α,β).  Modelled as a
-- recompute that ignores its Beta argument — so applying it twice is the same
-- as applying it once.  This is the formal counterpart of "evidence is
-- re-derived, not folded into a mutated scalar", the property Phase 2 lacked.
-- ---------------------------------------------------------------------------

recompute : (α₀ β₀ pos neg : ℕ) → Beta → Beta
recompute α₀ β₀ pos neg _ = mkBeta (α₀ + pos) (β₀ + neg)

recompute-idempotent :
  ∀ (α₀ β₀ pos neg : ℕ) (b : Beta) →
  recompute α₀ β₀ pos neg (recompute α₀ β₀ pos neg b)
    ≡ recompute α₀ β₀ pos neg b
recompute-idempotent _ _ _ _ _ = refl

-- ---------------------------------------------------------------------------
-- Decay anchor: the decay target (1,1) has mean exactly ½ (50%).
-- Decay pulls (α,β) toward (1,1); the full "mean moves monotonically toward ½"
-- trajectory is an operational property of the fractional pull (cf. Phase 2's
-- fixpoint convergence — bounded/operational, not proved here).  What IS proved
-- is the anchor it moves toward.
-- ---------------------------------------------------------------------------

decay-target-mean-is-½ : betaMean (mkBeta 1 1) ≡ mkProb 50
decay-target-mean-is-½ = refl

-- ---------------------------------------------------------------------------
-- Conjugate evidence accumulation (Phase 3 propagation).
-- A node's posterior count is its fixed prior plus the SUM of per-parent
-- evidence quanta (Δαᵢ = wᵢ·μᵢ·UNIT for support/causes onto α; Δβ onto β):
--   α = α₀ + Σ Δαᵢ,   β = β₀ + Σ Δβᵢ.
-- Because accumulation is a SUM, it is order-independent — the conjugate
-- analogue of Phase 2's product-based noisy-OR order-independence, and even
-- simpler (addition commutes). This REPLACES the noisy-OR/noisy-AND combine
-- that Phase 2's Inference.agda modelled.
-- ---------------------------------------------------------------------------

accumulate : ℕ → List ℕ → ℕ
accumulate prior []       = prior
accumulate prior (d ∷ ds) = d + accumulate prior ds

private
  +-swap : ∀ (a b c : ℕ) → a + (b + c) ≡ b + (a + c)
  +-swap a b c =
    trans (sym (+-assoc a b c))
      (trans (cong (_+ c) (+-comm a b)) (+-assoc b a c))

-- ORDER-INDEPENDENCE of conjugate accumulation: permuting the per-parent
-- evidence quanta leaves the accumulated count unchanged.
accumulate-↭ :
  ∀ (prior : ℕ) {xs ys} → xs P.↭ ys → accumulate prior xs ≡ accumulate prior ys
accumulate-↭ prior P.refl                   = refl
accumulate-↭ prior (P.prep x p)             = cong (x +_) (accumulate-↭ prior p)
accumulate-↭ prior (P.swap {xs} {ys} x y p) =
  trans (cong (λ z → x + (y + z)) (accumulate-↭ prior p))
        (+-swap x y (accumulate prior ys))
accumulate-↭ prior (P.trans p q)            = trans (accumulate-↭ prior p) (accumulate-↭ prior q)
