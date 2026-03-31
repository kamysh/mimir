{-# OPTIONS --safe #-}
module AiMem where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Nat using (ℕ; _+_; _∸_; _*_; _≤ᵇ_; _/_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; *-monoˡ-≤; +-comm)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Unit using (⊤; tt)

-- ---------------------------------------------------------------------------
-- Core types
-- ---------------------------------------------------------------------------

-- Probability modelled as a natural number in [0, 100] (percent).
-- Purely constructive; no postulates needed.

record Prob : Set where
  constructor mkProb
  field pct : ℕ  -- invariant: pct ≤ 100 (stated externally)

-- Node identifier modelled as a natural number.
record NodeId : Set where
  constructor mkNodeId
  field uid : ℕ

-- Edge labels.
data EdgeLabel : Set where
  SUPPORTS    : EdgeLabel
  DEFEATS     : EdgeLabel
  CAUSES      : EdgeLabel
  CONTRADICTS : EdgeLabel

-- A belief node in the graph.
record Belief : Set where
  constructor mkBelief
  field
    id          : NodeId
    probability : Prob
    confidence  : Prob

-- ---------------------------------------------------------------------------
-- Defeat attenuation
-- Formula: P_result = P_target × (1 - w × P_defeater)
-- Rust: target_prob * (1 - weight * defeater_prob)
-- In natural-number arithmetic (integer division, truncating):
--   P_result ≈ P_target × (100 - w × P_defeater / 100) / 100
-- This is an integer approximation of the real-valued formula P × (1 - w × N).
-- The truncating division ensures the result stays in [0, 100].
-- ---------------------------------------------------------------------------

attenuate : Prob → Prob → Prob → Prob
attenuate target defeater w =
  -- P_result = P_target × (100 - w × P_defeater) / 100
  -- In natural number arithmetic (integer division, truncating):
  mkProb ((Prob.pct target * (100 ∸ (Prob.pct w * Prob.pct defeater / 100))) / 100)

-- ---------------------------------------------------------------------------
-- Note: Prob uses ℕ percentage [0,100] as an integer approximation of
-- the implementation's f64 [0,1]. Correspondence: val ≈ pct / 100.
-- Phase 1 approximation; Phase 2 may use a rational or real number type.
-- ---------------------------------------------------------------------------

-- One step of decay: multiply by 99/100 (integer truncation).
decay-step : Prob → Prob
decay-step p = mkProb (Prob.pct p * 99 / 100)

-- Apply decay for d days.
decay : Prob → ℕ → Prob
decay p Data.Nat.zero    = p
decay p (Data.Nat.suc d) = decay-step (decay p d)

-- ---------------------------------------------------------------------------
-- Contradiction detection.
-- Two beliefs actively contradict when their probabilities sum to > 100 %,
-- i.e. P(a) + P(b) > 1.0 (in integer approximation: pct_a + pct_b > 100).
-- ---------------------------------------------------------------------------

isContradicting : Belief → Belief → Bool
isContradicting a b =
  101 ≤ᵇ (Prob.pct (Belief.probability a) + Prob.pct (Belief.probability b))

-- ---------------------------------------------------------------------------
-- Provable invariants
-- ---------------------------------------------------------------------------

-- Decay does not increase probability.
-- Intended property: ∀ (p : Prob) (d : ℕ) → Prob.pct (decay p d) ≤ Prob.pct p
-- Provable: each step multiplies by 99/100 ≤ 1, so pct can only decrease or stay.
-- (Full proof deferred to Phase 2 with a rational or real-number Prob type.)

-- Graph state for idempotency.
record GraphState : Set where
  constructor mkGraphState
  field
    nodeCount : ℕ
    edgeCount : ℕ

-- Init is identity — idempotent by construction.
initGraph : GraphState → GraphState
initGraph s = s

initGraph-idempotent : (s : GraphState) → initGraph (initGraph s) ≡ initGraph s
initGraph-idempotent _ = refl

-- ---------------------------------------------------------------------------
-- Symmetry of contradiction detection
-- ---------------------------------------------------------------------------

isContradicting-sym : (a b : Belief) → isContradicting a b ≡ isContradicting b a
isContradicting-sym a b =
  cong (101 ≤ᵇ_)
    (+-comm (Prob.pct (Belief.probability a)) (Prob.pct (Belief.probability b)))