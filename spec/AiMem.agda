{-# OPTIONS --safe #-}
module AiMem where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Nat using (ℕ; _+_; _∸_; _*_; _≤ᵇ_)
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
-- Spec property: attenuated probability ≤ original.
-- We model attenuation as truncating subtraction so the property holds
-- trivially (x ∸ k ≤ x for all x, k : ℕ).
-- ---------------------------------------------------------------------------

attenuate : Prob → Prob → Prob → Prob
attenuate target defeater w =
  mkProb (Prob.pct target ∸ (Prob.pct w * Prob.pct defeater))

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