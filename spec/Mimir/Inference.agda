{-# OPTIONS --safe #-}
module Mimir.Inference where

open import Mimir.Types
open import Data.Bool            using (Bool; true; false; _∧_; not)
open import Data.Nat             using (ℕ; _+_; _∸_; _*_; _/_; _^_; _≤_; _≤ᵇ_; _≡ᵇ_; z≤n; s≤s; NonZero)
open import Data.Nat.Properties  using (≤-refl; ≤-trans; ≤-reflexive; *-monoˡ-≤; *-mono-≤; *-assoc; *-comm; +-comm; m≤m+n; m∸n≤m; m^n≢0; ∸-monoʳ-≤; m∸[m∸n]≡n)
open import Data.Nat.DivMod      using (m*n/n≡m; /-monoˡ-≤)
open import Data.Product         using (_×_; _,_)
open import Data.List            using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Binary.Permutation.Propositional as P
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (↭-length)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; trans)

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
--
-- NAMING NOTE: graph.rs defines `Probability::attenuate(factor) → Self`
-- which computes P × factor (scalar multiply, clamped to [0,1]).  This is
-- a DIFFERENT operation from the `attenuate` function above.  The graph.rs
-- method is used ONLY in graph.rs unit tests — it does not participate in
-- propagation, decay, or contradiction detection.  The spec's `attenuate`
-- models `InferenceEngine::attenuate_by_defeat` (three-argument defeat
-- formula: target × (1 − weight × defeater)), not `Probability::attenuate`.
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

-- Private helper: m * k / 100 ≤ m whenever k ≤ 100.
-- Proof chain: m*k/100 = k*m/100 ≤ 100*m/100 = m*100/100 = m.
private
  m*k/100≤m : ∀ (m k : ℕ) → k ≤ 100 → m * k / 100 ≤ m
  m*k/100≤m m k k≤100 =
    ≤-trans
      (≤-reflexive (cong (_/ 100) (*-comm m k)))
      (≤-trans
        (/-monoˡ-≤ 100 (*-monoˡ-≤ m k≤100))
        (≤-reflexive
          (trans
            (cong (_/ 100) (sym (*-comm m 100)))
            (m*n/n≡m m 100))))

-- decay-step multiplies by 99/100, so result ≤ input.
decay-step-≤ : ∀ (p : Prob) → Prob.pct (decay-step p) ≤ Prob.pct p
decay-step-≤ p = m*k/100≤m (Prob.pct p) 99 (m≤m+n 99 1)

-- decay never increases probability (by induction on d).
decay-≤ : ∀ (p : Prob) (d : ℕ) → Prob.pct (decay p d) ≤ Prob.pct p
decay-≤ p Data.Nat.zero    = ≤-refl
decay-≤ p (Data.Nat.suc d) = ≤-trans (decay-step-≤ (decay p d)) (decay-≤ p d)

-- ---------------------------------------------------------------------------
-- Symmetry of contradiction detection
-- ---------------------------------------------------------------------------

isContradicting-sym : (a b : Belief) → isContradicting a b ≡ isContradicting b a
isContradicting-sym a b =
  cong (101 ≤ᵇ_)
    (+-comm (Prob.pct (Belief.probability a)) (Prob.pct (Belief.probability b)))

-- ---------------------------------------------------------------------------
-- Support boost
-- Formula: P_result = P + (100 − P) × w × S / 10 000  (integer truncation)
-- Rust:    target + (1 − target) × weight × supporter   (f64)
-- Applies to SUPPORTS and CAUSES edges during BFS propagation.
-- ---------------------------------------------------------------------------

boost : Prob → Prob → Prob → Prob
boost target supporter w =
  mkProb (Prob.pct target +
    (100 ∸ Prob.pct target) * Prob.pct w * Prob.pct supporter / 10000)

-- boost never decreases the target probability:
-- the added term is a natural number, so result = target + k ≥ target.
boost-never-decreases :
  ∀ (target supporter w : Prob) →
  Prob.pct target ≤ Prob.pct (boost target supporter w)
boost-never-decreases target supporter w =
  m≤m+n (Prob.pct target) _

-- ---------------------------------------------------------------------------
-- Configurable decay
-- Formula (one step): P_new = P × f / 100   where f ∈ [0, 100] is the
-- per-day retention factor (f = 99 ≈ the original hardcoded 0.99/day).
-- Rust: prob × decay_factor ^ days  where decay_factor ≈ f / 100.
-- The original `decay` / `decay-step` above hardcode f = 99; these are the
-- general versions used by the `decay_all` MCP tool.
-- ---------------------------------------------------------------------------

decay-step-f : Prob → ℕ → Prob
decay-step-f p f = mkProb (Prob.pct p * f / 100)

decay-f : Prob → ℕ → ℕ → Prob
decay-f p Data.Nat.zero    _ = p
decay-f p (Data.Nat.suc d) f = decay-step-f (decay-f p d f) f

-- decay-f recovers the original decay when f = 99:
decay-f-99-matches : ∀ (p : Prob) (d : ℕ) → decay-f p d 99 ≡ decay p d
decay-f-99-matches p Data.Nat.zero    = refl
decay-f-99-matches p (Data.Nat.suc d) = cong decay-step (decay-f-99-matches p d)

-- Configurable decay never increases (when f ≤ 100).
decay-f-step-≤ : ∀ (p : Prob) (f : ℕ) → f ≤ 100 → Prob.pct (decay-step-f p f) ≤ Prob.pct p
decay-f-step-≤ p f f≤100 = m*k/100≤m (Prob.pct p) f f≤100

decay-f-≤ : ∀ (p : Prob) (d : ℕ) (f : ℕ) → f ≤ 100 → Prob.pct (decay-f p d f) ≤ Prob.pct p
decay-f-≤ p Data.Nat.zero    _ _      = ≤-refl
decay-f-≤ p (Data.Nat.suc d) f f≤100 =
  ≤-trans (decay-f-step-≤ (decay-f p d f) f f≤100) (decay-f-≤ p d f f≤100)

-- ---------------------------------------------------------------------------
-- PHASE 3 NOTE: `decay-confidence` below models the PRE-Phase-3 scalar decay
-- (decay the confidence scalar only). Under Phase 3, decay instead pulls the
-- Beta counts (α,β) toward (1,1), moving BOTH the mean and the strength — see
-- Mimir.Beta (decay-target-mean-is-½). `decay-f` is kept as the legacy model.
-- ---------------------------------------------------------------------------
-- decay_all — the Rust inference engine decays the `confidence` field
-- (not `probability`) of every belief.  Correspondingly the spec applies
-- decay-f to Belief.confidence.
--
-- Only-if-changed filter (inference.rs):
--   if (decayed.value() - belief.confidence.value()).abs() > f64::EPSILON
-- A belief that was activated at the moment of the call (0 days elapsed)
-- produces decay_factor^0.0 = 1.0, so decayed == original and it is NOT
-- included in the result.  The spec's decay-confidence computes the value
-- unconditionally; the filter is applied by the service layer.
-- ---------------------------------------------------------------------------

decay-confidence : Belief → ℕ → ℕ → Prob
decay-confidence b days factor = decay-f (Belief.confidence b) days factor

-- PATTERNS EXEMPT FROM DECAY: `decay_all` calls `get_all_beliefs_for_decay`
-- which is an alias for `list_beliefs()`.  Only Belief vertices are returned;
-- Pattern vertices are never included.  Consequently Pattern.successRate is
-- NEVER modified by the decay mechanism — it is write-once at creation.
-- Formal witness: decay-confidence is typed `Belief → ℕ → ℕ → Prob`.
-- There is no decay-pattern function; none is needed.

-- decay_all MCP RETURN FORMAT: the tool returns {"decayed": count} where
-- `count` is the number of beliefs whose confidence actually changed
-- (filtered by `|decayed - original| > f64::EPSILON`).  Beliefs activated
-- at the moment of the call (0 days elapsed) are NOT counted — they are
-- excluded because decay_factor^0 = 1.0 and (1.0 - 1.0).abs() = 0 ≤ EPSILON.
-- The JSON key is "decayed" (not "count" or "updated").

-- ---------------------------------------------------------------------------
-- Single-step edge primitives (per-edge monotonicity).
-- PHASE 3 NOTE: `attenuate` / `boost` are standalone single-edge primitives.
-- They no longer drive propagation — Phase 3 replaced the Phase-2 noisy-OR /
-- noisy-AND combine with Bayesian conjugate accumulation in Beta (α,β) space,
-- modelled in Mimir.Beta: accumulate-↭ (order-independence, sum form),
-- support-mono / defeat-anti (mean monotonicity), and recompute-idempotent. The
-- lemmas below remain valid for the Rust `attenuate_by_defeat` /
-- `boost_by_support` primitives (still present, exercised by their own tests).
--
-- DEFEATS: attenuate(target, defeater, w) ≤ target
attenuate-≤ : ∀ (target defeater w : Prob) →
  Prob.pct (attenuate target defeater w) ≤ Prob.pct target
attenuate-≤ target defeater w =
  m*k/100≤m (Prob.pct target)
             (100 ∸ (Prob.pct w * Prob.pct defeater / 100))
             (m∸n≤m 100 (Prob.pct w * Prob.pct defeater / 100))
--
-- SUPPORTS / CAUSES: boost(target, supporter, w) ≥ target
-- Proved above as boost-never-decreases.
--
-- CONTRADICTS: skipped during propagation (inference.rs line: `EdgeType::Contradicts => continue`).
-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- (The Phase-2 noisy-OR / noisy-AND multi-edge combine that used to live here
-- has been removed. Phase 3 replaced it with Bayesian conjugate accumulation,
-- modelled in Mimir.Beta — see `accumulate-↭` there for the order-independence
-- property this section used to prove, and `support-mono` / `defeat-anti` for
-- the mean monotonicity.)
-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- The do-operator (Phase 1): interventional semantics for CAUSES edges
--
-- Rust: InferenceEngine::intervene(target, value, downstream, edges) performs
-- Pearl's graph mutilation —
--   edges.filter(|&(_from, to, et, _w)| to != target_id && et == Causes)
-- — then propagates forward along the surgical edge set. The structural
-- content of mutilation is: NO surviving edge points into the intervened node
-- (its value is independent of its former parents). That is the lemma proved
-- below. RRF/cosine and the numeric BFS are runtime concerns not modelled in
-- --safe Agda; here we model only the edge-set surgery and its key property.
-- ---------------------------------------------------------------------------

-- Boolean equality on node identifiers (compares the underlying ℕ uid).
nodeEqᵇ : NodeId → NodeId → Bool
nodeEqᵇ a b = NodeId.uid a ≡ᵇ NodeId.uid b

-- Whether an edge label is CAUSES (the only label an intervention follows).
isCausesᵇ : EdgeLabel → Bool
isCausesᵇ SUPPORTS    = false
isCausesᵇ DEFEATS     = false
isCausesᵇ CAUSES      = true
isCausesᵇ CONTRADICTS = false

-- A directed, labelled, weighted edge between two belief nodes.
record Edge : Set where
  constructor mkEdge
  field
    fromId : NodeId
    toId   : NodeId
    label  : EdgeLabel
    weight : Prob

-- Keep an edge under do(t = …) iff it is a CAUSES edge AND does not point
-- into the intervened node t. Mirrors the Rust filter predicate exactly:
--   to != target_id && et == Causes
keepForIntervention : NodeId → Edge → Bool
keepForIntervention t e = isCausesᵇ (Edge.label e) ∧ not (nodeEqᵇ (Edge.toId e) t)

-- Graph surgery: the surviving edge set after intervening on t.
surgical : NodeId → List Edge → List Edge
surgical t []       = []
surgical t (e ∷ es) with keepForIntervention t e
... | true  = e ∷ surgical t es
... | false = surgical t es

-- Boolean helper lemmas.
private
  ∧-elimʳ : ∀ (a b : Bool) → (a ∧ b) ≡ true → b ≡ true
  ∧-elimʳ true  b eq = eq
  ∧-elimʳ false b ()

  not-true→false : ∀ (x : Bool) → not x ≡ true → x ≡ false
  not-true→false false _  = refl
  not-true→false true  ()

-- INTERVENE-IGNORES-PARENTS: after surgery on t, no surviving edge points into
-- t. Equivalently, every edge in `surgical t es` has `toId ≢ t` (its boolean
-- equality test is false). This is the formal content of graph mutilation —
-- the intervened node's value is independent of its former parents.
surgical-ignores-parents :
  ∀ (t : NodeId) (es : List Edge) →
  All (λ e → nodeEqᵇ (Edge.toId e) t ≡ false) (surgical t es)
surgical-ignores-parents t []       = []
surgical-ignores-parents t (e ∷ es) with keepForIntervention t e in eq
... | true  =
  not-true→false (nodeEqᵇ (Edge.toId e) t)
    (∧-elimʳ (isCausesᵇ (Edge.label e)) (not (nodeEqᵇ (Edge.toId e) t)) eq)
  ∷ surgical-ignores-parents t es
... | false = surgical-ignores-parents t es

-- Corollary: every surviving edge is a CAUSES edge — non-causal (evidential)
-- paths are cut, which is what distinguishes intervention from observation.
surgical-only-causes :
  ∀ (t : NodeId) (es : List Edge) →
  All (λ e → isCausesᵇ (Edge.label e) ≡ true) (surgical t es)
surgical-only-causes t []       = []
surgical-only-causes t (e ∷ es) with keepForIntervention t e in eq
... | true  =
  ∧-elimˡ (isCausesᵇ (Edge.label e)) (not (nodeEqᵇ (Edge.toId e) t)) eq
  ∷ surgical-only-causes t es
  where
    ∧-elimˡ : ∀ (a b : Bool) → (a ∧ b) ≡ true → a ≡ true
    ∧-elimˡ true  b _  = refl
    ∧-elimˡ false b ()
... | false = surgical-only-causes t es
