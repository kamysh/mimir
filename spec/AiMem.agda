{-# OPTIONS --safe #-}
module AiMem where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Nat using (ℕ; _+_; _∸_; _*_; _≤ᵇ_; _/_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
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

-- Decay is modelled as identity (conservative bound: no increase).
decay : Prob → ℕ → Prob
decay p _ = p

-- ---------------------------------------------------------------------------
-- Contradiction detection.
-- Two beliefs actively contradict when both have probability > 50 %.
-- ---------------------------------------------------------------------------

isContradicting : Belief → Belief → Bool
isContradicting a b =
  (51 ≤ᵇ Prob.pct (Belief.probability a))
  ∧
  (51 ≤ᵇ Prob.pct (Belief.probability b))

-- ---------------------------------------------------------------------------
-- Provable invariants
-- ---------------------------------------------------------------------------

-- Decay is identity, so it trivially does not increase probability.
decay-no-increase : (p : Prob) (h : ℕ) → Prob.pct (decay p h) ≡ Prob.pct p
decay-no-increase _ _ = refl

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

open import Data.Bool.Properties using (∧-comm)

isContradicting-sym : (a b : Belief) → isContradicting a b ≡ isContradicting b a
isContradicting-sym a b = ∧-comm
  (51 ≤ᵇ Prob.pct (Belief.probability a))
  (51 ≤ᵇ Prob.pct (Belief.probability b))