{-# OPTIONS --safe #-}
-- Phase 3 — beliefs as Beta(α, β), over the rationals ℚ.
--
-- A belief's evidence state is a Beta distribution with rational pseudo-counts
-- α, β (ℚ, both ≥ 0):
--   mean      = α / (α + β)   (the value the rest of the system reads as "probability")
--   strength  = α + β         (pseudo-count; what "confidence" was gesturing at)
--
-- The prior (α₀, β₀) is fixed at insertion; the posterior is recomputed as
-- (α₀ + Σ pos_evidence, β₀ + Σ neg_evidence) from the edge structure on each
-- propagation — so propagation is IDEMPOTENT (re-deriving evidence cannot drift).
--
-- WHY ℚ (not ℕ): decay is a FRACTIONAL pull of (α,β) toward (1,1):
--   decay (α,β) f = (1 + f·(α−1), 1 + f·(β−1)),  f ∈ [0,1].
-- ℕ cannot represent that, so the whole model is over ℚ. ℚ division is exact,
-- so the mean is a real value and the monotonicity proofs are exact.
--
-- MEAN COMPARISON is stated by CROSS-MULTIPLICATION over ℚ:
--   mean b₁ ≤ mean b₂  ⟺  α₁·(α₂+β₂) ≤ α₂·(α₁+β₁)
-- This is the exact rational order and needs only *,+ monotonicity (no division
-- lemmas). Positivity of α,β is the real-world invariant (counts are ≥ 0); it is
-- carried as explicit NonNegative hypotheses where a proof needs it.
module Mimir.Beta where

open import Data.Rational using (ℚ; 0ℚ; 1ℚ; ½; _+_; _-_; _*_; _÷_; -_; _≤_; NonZero; NonNegative)
open import Data.Rational.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; *-comm; +-comm; +-assoc;
         *-distribˡ-+; *-distribʳ-+;
         *-monoˡ-≤-nonNeg; *-monoʳ-≤-nonNeg; +-monoʳ-≤; +-mono-≤;
         +-identityʳ; nonNegative⁻¹; *-zeroˡ; *-identityˡ; +-inverseˡ)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; []; _∷_)
import Data.List.Relation.Binary.Permutation.Propositional as P
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; trans)

-- ---------------------------------------------------------------------------
-- The Beta state (rational pseudo-counts)
-- ---------------------------------------------------------------------------

record Beta : Set where
  constructor mkBeta
  field
    α : ℚ
    β : ℚ

open Beta

-- Pseudo-count strength α + β.
strength : Beta → ℚ
strength b = α b + β b

-- The mean as a rational, α / (α+β).  Exact ℚ division; needs α+β ≠ 0, supplied
-- as an instance at concrete use sites.
betaMean : (b : Beta) → .{{NonZero (strength b)}} → ℚ
betaMean b = α b ÷ strength b

-- Cross-multiplied "mean b₁ ≤ mean b₂": α₁·(α₂+β₂) ≤ α₂·(α₁+β₁).
mean≤ : Beta → Beta → Set
mean≤ b₁ b₂ = α b₁ * strength b₂ ≤ α b₂ * strength b₁

-- ---------------------------------------------------------------------------
-- Helper: p ≤ p + q when q ≥ 0 (derived; stdlib has no p≤p+q export for ℚ).
-- p = p + 0 ≤ p + q  by monotonicity of + in its right argument.
-- ---------------------------------------------------------------------------
p≤p+nonNeg : ∀ (p q : ℚ) → .{{NonNegative q}} → p ≤ p + q
p≤p+nonNeg p q = ≤-trans (≤-reflexive (sym (+-identityʳ p)))
                         (+-monoʳ-≤ p (nonNegative⁻¹ q))

-- ---------------------------------------------------------------------------
-- (1) mean ∈ [0,1].  As a rational, α/(α+β) ≤ 1 ⟺ α ≤ α+β (needs β ≥ 0).
-- ---------------------------------------------------------------------------

mean-≤1 : ∀ (b : Beta) → .{{NonNegative (β b)}} → α b ≤ strength b
mean-≤1 b = p≤p+nonNeg (α b) (β b)

-- ---------------------------------------------------------------------------
-- (3) Defeat increases β ⇒ mean does not increase.
--   mean (α, β+d) ≤ mean (α, β).  Numerator α fixed, denominator grows:
--   α·(α+β) ≤ α·(α+(β+d)), i.e. α·strength b ≤ α·strength(defeated).
-- ---------------------------------------------------------------------------

defeat-anti : ∀ (b : Beta) (d : ℚ) → .{{NonNegative (α b)}} → .{{NonNegative d}}
  → mean≤ (mkBeta (α b) (β b + d)) b
defeat-anti b d =
  *-monoˡ-≤-nonNeg (α b) (+-monoʳ-≤ (α b) (p≤p+nonNeg (β b) d))

-- ---------------------------------------------------------------------------
-- (2) Support increases α ⇒ mean does not decrease.
--   mean (α, β) ≤ mean (α+d, β).
-- Cross-product goal: α·((α+d)+β) ≤ (α+d)·(α+β).
--   LHS = α·(α+β) + α·d           (distribute)
--   RHS = α·(α+β) + d·(α+β)       (distribute)
-- so it reduces to α·d ≤ d·(α+β), i.e. α·d ≤ d·strength, which holds because
-- d ≥ 0 and α ≤ strength (mean-≤1).
-- ---------------------------------------------------------------------------

support-mono : ∀ (b : Beta) (d : ℚ)
  → .{{NonNegative (α b)}} → .{{NonNegative (β b)}} → .{{NonNegative d}}
  → mean≤ b (mkBeta (α b + d) (β b))
support-mono b d = goal
  where
    a = α b
    c = β b
    lemma-assoc : ∀ (x y z : ℚ) → (x + y) + z ≡ (x + z) + y
    lemma-assoc x y z =
      trans (+-assoc x y z)
        (trans (cong (x +_) (+-comm y z)) (sym (+-assoc x z y)))
    -- α·d ≤ d·(α+β):  α·d = d·α (comm) ≤ d·(α+β) (mono, d ≥ 0).
    ad≤ : a * d ≤ d * (a + c)
    ad≤ = ≤-trans (≤-reflexive (*-comm a d))
                  (*-monoˡ-≤-nonNeg d (p≤p+nonNeg a c))
    mid : a * (a + c) + a * d ≤ a * (a + c) + d * (a + c)
    mid = +-monoʳ-≤ (a * (a + c)) ad≤
    eqL : a * ((a + d) + c) ≡ a * (a + c) + a * d
    eqL = trans (cong (a *_) (lemma-assoc a d c))
                (*-distribˡ-+ a (a + c) d)
    eqR : a * (a + c) + d * (a + c) ≡ (a + d) * (a + c)
    eqR = sym (*-distribʳ-+ (a + c) a d)
    goal : a * ((a + d) + c) ≤ (a + d) * (a + c)
    goal = ≤-trans (≤-reflexive eqL) (≤-trans mid (≤-reflexive eqR))

-- ---------------------------------------------------------------------------
-- (4) Idempotence of conjugate recomputation.
-- The posterior is re-derived from the FIXED prior (α₀,β₀) plus the evidence
-- sums (pos,neg); it never reads the belief's current (α,β).  Modelled as a
-- recompute that ignores its Beta argument — applying it twice = once.
-- ---------------------------------------------------------------------------

recompute : (α₀ β₀ pos neg : ℚ) → Beta → Beta
recompute α₀ β₀ pos neg _ = mkBeta (α₀ + pos) (β₀ + neg)

recompute-idempotent :
  ∀ (α₀ β₀ pos neg : ℚ) (b : Beta) →
  recompute α₀ β₀ pos neg (recompute α₀ β₀ pos neg b)
    ≡ recompute α₀ β₀ pos neg b
recompute-idempotent _ _ _ _ _ = refl

-- ---------------------------------------------------------------------------
-- Conjugate evidence accumulation (Phase 3 propagation), over ℚ.
-- A node's posterior count is its fixed prior plus the SUM of per-parent
-- evidence quanta (Δαᵢ = wᵢ·μᵢ·UNIT for support/causes onto α; Δβ onto β):
--   α = α₀ + Σ Δαᵢ,   β = β₀ + Σ Δβᵢ.
-- Because accumulation is a SUM, it is order-independent (addition commutes).
-- ---------------------------------------------------------------------------

accumulate : ℚ → List ℚ → ℚ
accumulate prior []       = prior
accumulate prior (d ∷ ds) = d + accumulate prior ds

private
  +-swap : ∀ (a b c : ℚ) → a + (b + c) ≡ b + (a + c)
  +-swap a b c =
    trans (sym (+-assoc a b c))
      (trans (cong (_+ c) (+-comm a b)) (+-assoc b a c))

-- ORDER-INDEPENDENCE: permuting the per-parent evidence quanta leaves the
-- accumulated count unchanged.
accumulate-↭ :
  ∀ (prior : ℚ) {xs ys} → xs P.↭ ys → accumulate prior xs ≡ accumulate prior ys
accumulate-↭ prior P.refl                   = refl
accumulate-↭ prior (P.prep x p)             = cong (x +_) (accumulate-↭ prior p)
accumulate-↭ prior (P.swap {xs} {ys} x y p) =
  trans (cong (λ z → x + (y + z)) (accumulate-↭ prior p))
        (+-swap x y (accumulate prior ys))
accumulate-↭ prior (P.trans p q)            = trans (accumulate-↭ prior p) (accumulate-↭ prior q)

-- ---------------------------------------------------------------------------
-- EVIDENCE COMPLETENESS (the property propagation must satisfy).
--
-- A node's posterior is re-derived from its FIXED prior plus the evidence of
-- its parents.  The evidence set MUST be the node's COMPLETE set of incoming
-- edges — NOT a subgraph-local subset.  Re-deriving from prior + a SUBSET of
-- the incoming edges silently discards the evidence of the omitted parents
-- (the exact failure: propagating from one seed must not erase a belief's
-- support that came from a parent outside that seed's reachable subgraph).
--
-- We model an evidence edge as (source-mean, weight, polarity).  posteriorOf
-- builds (α,β) from the prior plus EVERY edge incident to the node; the
-- completeness lemma states that dropping any incoming edge changes the result
-- by exactly that edge's quantum — so omitting evidence is observable, never
-- silent.  EVIDENCE_UNIT is the spec's quantum scale (impl: graph.rs).
-- ---------------------------------------------------------------------------

data Polarity : Set where
  pos : Polarity   -- SUPPORTS / CAUSES → onto α
  neg : Polarity   -- DEFEATS         → onto β

record InEdge : Set where
  constructor mkIn
  field
    srcMean  : ℚ          -- the parent's current mean μ
    weight   : ℚ          -- edge weight w
    polarity : Polarity

open InEdge

-- One edge's evidence quantum Δ = w · μ.  (The fixed UNIT scale is a global
-- constant folded in at the impl; here Δ is w·μ and the proofs are scale-free.)
quantum : InEdge → ℚ
quantum e = weight e * srcMean e

-- α and β are each the prior plus the SUM of the quanta of the edges of that
-- polarity — over the COMPLETE incoming-edge list `es`.
posteriorα : ℚ → List InEdge → ℚ
posteriorα α₀ []       = α₀
posteriorα α₀ (e ∷ es) with polarity e
... | pos = quantum e + posteriorα α₀ es
... | neg = posteriorα α₀ es

posteriorβ : ℚ → List InEdge → ℚ
posteriorβ β₀ []       = β₀
posteriorβ β₀ (e ∷ es) with polarity e
... | pos = posteriorβ β₀ es
... | neg = quantum e + posteriorβ β₀ es

posteriorOf : (α₀ β₀ : ℚ) → List InEdge → Beta
posteriorOf α₀ β₀ es = mkBeta (posteriorα α₀ es) (posteriorβ β₀ es)

-- COMPLETENESS: prepending one more incoming POS edge adds exactly its quantum
-- to α (and leaves β alone).  Contrapositive: leaving that edge OUT of `es`
-- yields an α short by exactly `quantum e` — i.e. omitting an incoming edge is
-- observable in the posterior, so a correct propagation cannot silently drop a
-- parent's evidence.
posteriorα-pos-cons :
  ∀ (α₀ : ℚ) (e : InEdge) (es : List InEdge) → polarity e ≡ pos →
  posteriorα α₀ (e ∷ es) ≡ quantum e + posteriorα α₀ es
posteriorα-pos-cons α₀ e es p rewrite p = refl

posteriorβ-neg-cons :
  ∀ (β₀ : ℚ) (e : InEdge) (es : List InEdge) → polarity e ≡ neg →
  posteriorβ β₀ (e ∷ es) ≡ quantum e + posteriorβ β₀ es
posteriorβ-neg-cons β₀ e es p rewrite p = refl

-- A pos edge does not touch β; a neg edge does not touch α (the two axes are
-- independent, as in support-mono / defeat-anti).
posteriorβ-pos-skip :
  ∀ (β₀ : ℚ) (e : InEdge) (es : List InEdge) → polarity e ≡ pos →
  posteriorβ β₀ (e ∷ es) ≡ posteriorβ β₀ es
posteriorβ-pos-skip β₀ e es p rewrite p = refl

posteriorα-neg-skip :
  ∀ (α₀ : ℚ) (e : InEdge) (es : List InEdge) → polarity e ≡ neg →
  posteriorα α₀ (e ∷ es) ≡ posteriorα α₀ es
posteriorα-neg-skip α₀ e es p rewrite p = refl

-- ---------------------------------------------------------------------------
-- Decay: a fractional pull of (α,β) toward the uninformative prior (1,1).
--   betaDecay (α,β) f = (1 + f·(α−1), 1 + f·(β−1)),   f ∈ [0,1].
-- f is the retention factor (= decay_factor ^ days_since_activation).
-- Endpoints are exact:
--   f = 0  →  collapses to (1,1)  (all evidence forgotten),
--   f = 1  →  identity            (no decay).
-- The decay target (1,1) has mean exactly ½.  The full monotone-toward-½
-- trajectory for intermediate f is operational (a property of the convex
-- pull) and not proved here; the transformation and both endpoints ARE.
-- ---------------------------------------------------------------------------

-- The retention factor f is a probability-like quantity: f = decay_factor^days
-- with decay_factor ∈ [0,1], so f ∈ [0,1].  This is the DOMAIN of betaDecay —
-- the implementation must reject a decay_factor outside [0,1] (an out-of-domain
-- f anti-decays, pushing (α,β) AWAY from (1,1), which is not decay).
ValidDecayFactor : ℚ → Set
ValidDecayFactor f = (0ℚ ≤ f) × (f ≤ 1ℚ)

-- The two proved endpoints lie in the domain (sanity: the domain is inhabited
-- exactly where the endpoint lemmas apply).
0-valid : ValidDecayFactor 0ℚ
0-valid = ≤-refl , 0≤1
  where 0≤1 : 0ℚ ≤ 1ℚ
        0≤1 = nonNegative⁻¹ 1ℚ

1-valid : ValidDecayFactor 1ℚ
1-valid = 0≤1 , ≤-refl
  where 0≤1 : 0ℚ ≤ 1ℚ
        0≤1 = nonNegative⁻¹ 1ℚ

betaDecay : Beta → ℚ → Beta
betaDecay b f = mkBeta (1ℚ + f * (α b - 1ℚ)) (1ℚ + f * (β b - 1ℚ))

-- f = 0: every count collapses to 1 — the uninformative prior (1,1).
betaDecay-0 : ∀ (b : Beta) → betaDecay b 0ℚ ≡ mkBeta 1ℚ 1ℚ
betaDecay-0 b = cong₂ mkBeta (one+0 (α b - 1ℚ)) (one+0 (β b - 1ℚ))
  where
    one+0 : ∀ (x : ℚ) → 1ℚ + 0ℚ * x ≡ 1ℚ
    one+0 x = trans (cong (1ℚ +_) (*-zeroˡ x)) (+-identityʳ 1ℚ)

-- f = 1: decay is the identity (1 + 1·(x−1) = x).
betaDecay-1 : ∀ (b : Beta) → betaDecay b 1ℚ ≡ b
betaDecay-1 b = cong₂ mkBeta (one+id (α b)) (one+id (β b))
  where
    one+id : ∀ (x : ℚ) → 1ℚ + 1ℚ * (x - 1ℚ) ≡ x
    one+id x = trans (cong (1ℚ +_) (*-identityˡ (x - 1ℚ))) (one+x-1 x)
      where
        -- 1 + (x − 1) ≡ x
        one+x-1 : ∀ (y : ℚ) → 1ℚ + (y - 1ℚ) ≡ y
        one+x-1 y = trans (+-comm 1ℚ (y - 1ℚ)) (y-1+1 y)
          where
            -- (y − 1) + 1 ≡ y
            y-1+1 : ∀ (z : ℚ) → (z - 1ℚ) + 1ℚ ≡ z
            y-1+1 z = trans (+-assoc z (- 1ℚ) 1ℚ)
                            (trans (cong (z +_) (+-inverseˡ 1ℚ)) (+-identityʳ z))

-- The decay target (1,1) has mean exactly ½.
decay-target-mean-is-½ : betaMean (mkBeta 1ℚ 1ℚ) ≡ ½
decay-target-mean-is-½ = refl

-- ---------------------------------------------------------------------------
-- Persistence contract.
-- The DURABLE belief state is four rationals: the posterior (α,β) and the
-- FIXED prior (α₀,β₀).  The derived scalars (mean, strength — i.e. what older
-- code called probability/confidence) are NOT stored; they are recomputed on
-- load via betaMean / strength.  This is the contract that insert_belief /
-- update_belief_beta / belief_from_row must satisfy.
--
-- BetaWithPrior bundles posterior + prior; StoredBelief is the on-disk row.
-- store/load are projections, and the round-trip is the identity — so loading
-- back what was stored reproduces the belief state exactly (no lossy scalar
-- round-trip, unlike the retired probability/confidence setters).
-- ---------------------------------------------------------------------------

record BetaWithPrior : Set where
  constructor mkBWP
  field
    posterior : Beta   -- current (α, β)
    prior     : Beta   -- fixed (α₀, β₀)

record StoredBelief : Set where
  constructor mkStored
  field
    sα sβ sα₀ sβ₀ : ℚ

store : BetaWithPrior → StoredBelief
store (mkBWP (mkBeta a b) (mkBeta a₀ b₀)) = mkStored a b a₀ b₀

load : StoredBelief → BetaWithPrior
load (mkStored a b a₀ b₀) = mkBWP (mkBeta a b) (mkBeta a₀ b₀)

-- Round-trip: loading a stored belief reproduces it exactly.
store-load-round-trip : ∀ (b : BetaWithPrior) → load (store b) ≡ b
store-load-round-trip (mkBWP (mkBeta _ _) (mkBeta _ _)) = refl

-- ---------------------------------------------------------------------------
-- C-coupling (Phase 4, second layer).
--
-- A GROUNDS edge of weight w is a pseudo-observation that bumps α by k·w
-- (evidence-mass constant k : ℚ, k ≥ 0).  β is unchanged.  This is a
-- principled Bayesian update — exactly the support-mono case with d = k·w.
--
-- Three properties are proved:
--  (1) coupling-increases-mean     : mean does not decrease (from support-mono)
--  (2) coupling-preserves-β        : β is unchanged (by refl)
--  (3) coupling-increases-strength : α+β grows, so betaDecay pulls less hard
--  (4) coupleAll-α                 : iterated coupling accumulates groundingMass
-- ---------------------------------------------------------------------------

module CCoupling (k : ℚ) where

  -- Apply one pseudo-observation of weight w: α += k·w, β unchanged.
  coupleOne : ℚ → Beta → Beta
  coupleOne w b = mkBeta (α b + k * w) (β b)

  -- (1) Coupling never lowers the mean (α ≥ 0, β ≥ 0, k*w ≥ 0 required).
  coupling-increases-mean :
    ∀ (b : Beta) (w : ℚ)
    → .{{NonNegative (α b)}} → .{{NonNegative (β b)}} → .{{NonNegative (k * w)}}
    → mean≤ b (coupleOne w b)
  coupling-increases-mean b w = support-mono b (k * w)

  -- (2) β is untouched.
  coupling-preserves-β : ∀ (b : Beta) (w : ℚ) → β (coupleOne w b) ≡ β b
  coupling-preserves-β b w = refl

  -- (3) strength (coupleOne w b) ≥ strength b  (when k*w ≥ 0).
  --     strength b = α b + β b ≤ (α b + k*w) + β b = strength (coupleOne w b).
  coupling-increases-strength :
    ∀ (b : Beta) (w : ℚ) → .{{NonNegative (k * w)}}
    → strength b ≤ strength (coupleOne w b)
  coupling-increases-strength b w =
    +-mono-≤ (p≤p+nonNeg (α b) (k * w)) ≤-refl

  -- Total grounding mass for a list of evidence weights: Σᵢ k·wᵢ.
  groundingMass : List ℚ → ℚ
  groundingMass []       = 0ℚ
  groundingMass (w ∷ ws) = k * w + groundingMass ws

  -- Apply all evidence weights, innermost first.
  coupleAll : List ℚ → Beta → Beta
  coupleAll []       b = b
  coupleAll (w ∷ ws) b = coupleOne w (coupleAll ws b)

  -- (4) α after coupleAll ws = original α + groundingMass ws.
  coupleAll-α :
    ∀ (ws : List ℚ) (b : Beta) →
    α (coupleAll ws b) ≡ α b + groundingMass ws
  coupleAll-α []       b = sym (+-identityʳ (α b))
  coupleAll-α (w ∷ ws) b =
    trans (cong (_+ k * w) (coupleAll-α ws b))
          (trans (+-assoc (α b) (groundingMass ws) (k * w))
                 (cong (α b +_) (+-comm (groundingMass ws) (k * w))))
