{-# OPTIONS --safe #-}
-- ---------------------------------------------------------------------------
-- Mimir.Evidence — document-grounded beliefs (Phase 4 C-core).
--
-- A DocumentChunk grounds a Belief via a GROUNDS edge. The hard invariant is
-- STRUCTURAL NON-INTERFERENCE: the evidence overlay does not add edges to
-- belief↔belief inference. Numerical C-coupling changes priors separately
-- (Mimir.Beta.CCoupling); it is not numerical posterior invariance.
--
-- The Rust side enforces it structurally: GROUNDS originates at a
-- :DocumentChunk and is NOT in {SUPPORTS, DEFEATS, CAUSES, CONTRADICTS}, while
-- get_downstream_beliefs / get_edges_among match (:Belief)->(:Belief) only. So
-- no GROUNDS edge ever enters the edge set fed to propagation.
--
-- Here we model that cleanly: a graph is a belief-edge substrate (the inference
-- input, reusing Mimir.Inference.Edge) plus a DISJOINT evidence overlay
-- (GROUNDS edges, a separate type — NOT added to EdgeLabel, mirroring the Rust
-- EdgeType). Propagation is a function of the substrate alone; we prove the
-- substrate is invariant under any evidence overlay, hence propagation is too.
-- ---------------------------------------------------------------------------
module Mimir.Evidence where

open import Mimir.Types     using (NodeId; Prob; mkProb)
open import Mimir.Inference using (Edge)
open import Data.Bool       using (Bool; true; false; _∧_)
open import Data.List       using (List; []; _∷_; _++_)
open import Data.Maybe      using (Maybe; just; nothing)
open import Data.String     using (String; _≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (does)
open import Data.Nat using (ℕ)

-- Abstract vector carrier for these structural grounding laws. Current
-- backend/vector validation and publication live in EmbeddingService and
-- DocumentStore; the unused document-summary proposal has been removed.
Embedding : Set
Embedding = List ℕ

-- A GROUNDS edge: a DocumentChunk (source) grounds a Belief (target) with a
-- weight. Deliberately a SEPARATE type from Edge — it carries no inference
-- label and can never appear in the belief-edge substrate.
record EvidenceEdge : Set where
  constructor mkEvidence
  field
    source : NodeId   -- a DocumentChunk
    target : NodeId   -- a Belief
    weight : Prob

-- A graph: the belief-edge substrate that inference reads, plus the evidence
-- overlay that it does not.
record Graph : Set where
  constructor mkGraph
  field
    beliefEdges   : List Edge          -- inference substrate
    evidenceEdges : List EvidenceEdge  -- provenance overlay

-- Inference reads ONLY the belief edges. This mirrors get_edges_among /
-- get_downstream_beliefs, which match (:Belief)->(:Belief) and never traverse
-- a GROUNDS edge.
inferenceSubstrate : Graph → List Edge
inferenceSubstrate g = Graph.beliefEdges g

-- Attaching one evidence edge: it lands in the overlay, never the substrate.
addEvidence : EvidenceEdge → Graph → Graph
addEvidence e g = mkGraph (Graph.beliefEdges g) (e ∷ Graph.evidenceEdges g)

-- Attaching a whole overlay.
overlay : List EvidenceEdge → Graph → Graph
overlay []       g = g
overlay (e ∷ es) g = addEvidence e (overlay es g)

-- ---------------------------------------------------------------------------
-- Non-interference
-- ---------------------------------------------------------------------------

-- A single evidence edge leaves the inference substrate untouched.
addEvidence-preserves-substrate :
  ∀ (e : EvidenceEdge) (g : Graph) →
  inferenceSubstrate (addEvidence e g) ≡ inferenceSubstrate g
addEvidence-preserves-substrate e g = refl

-- Any evidence overlay leaves the inference substrate untouched.
overlay-preserves-substrate :
  ∀ (es : List EvidenceEdge) (g : Graph) →
  inferenceSubstrate (overlay es g) ≡ inferenceSubstrate g
overlay-preserves-substrate []       g = refl
overlay-preserves-substrate (e ∷ es) g = overlay-preserves-substrate es g

-- THEOREM (non-interference). For ANY propagation function defined on the
-- substrate, and any evidence overlay, the result on the overlaid graph equals
-- the result on the bare graph. This is the formal counterpart of the
-- operational theorem in proposal 60: propagate g ≡ propagate (g ⊎ overlay e).
-- Because `propagate` is universally quantified, the existing Mimir.Inference
-- proofs remain applicable to the unchanged edge substrate. This statement
-- fixes all inputs other than the edge list; it does not hold priors fixed
-- while simultaneously claiming to model numerical C-coupling.
propagate-evidence-invariant :
  ∀ {A : Set} (propagate : List Edge → A)
    (es : List EvidenceEdge) (g : Graph) →
  propagate (inferenceSubstrate (overlay es g)) ≡ propagate (inferenceSubstrate g)
propagate-evidence-invariant propagate es g =
  cong propagate (overlay-preserves-substrate es g)

-- Similarity ranks candidate passages. Indexing alone never creates evidence
-- edges. Belief publication requires a validated supporting passage from an
-- indexed document and a prepared embedding.

-- Numerical bridge to C-coupling. The edge list includes fixed incoming
-- quanta; changed source means in a cascade require a new recomputation.
-- This is not a global linearity claim about graph fixed points.
module Numerical where
  import Mimir.Beta as B
  open import Data.Rational using (ℚ; _+_)
  open import Data.Rational.Properties using (+-assoc)
  open import Relation.Binary.PropositionalEquality using (sym; trans)

  posterior-base-offset : ∀ base offset es →
    B.posteriorα (base + offset) es ≡ B.posteriorα base es + offset
  posterior-base-offset base offset [] = refl
  posterior-base-offset base offset (e ∷ es) with B.InEdge.polarity e
  ... | B.pos = trans
    (cong (B.quantum e +_) (posterior-base-offset base offset es))
    (sym (+-assoc (B.quantum e) (B.posteriorα base es) offset))
  ... | B.neg = posterior-base-offset base offset es

  -- Independent review and grounding contributions enter the fixed prior;
  -- neither is taken from the previous posterior (which would count twice).
  recompute : ℚ → ℚ → ℚ → ℚ → ℚ → List B.InEdge → B.Beta
  recompute baseα baseβ reviewα reviewβ grounding es =
    B.posteriorOf ((baseα + reviewα) + grounding) (baseβ + reviewβ) es

  grounding-survives-recompute : ∀ baseα baseβ reviewα reviewβ grounding es →
    B.Beta.α (recompute baseα baseβ reviewα reviewβ grounding es) ≡
    B.posteriorα (baseα + reviewα) es + grounding
  grounding-survives-recompute baseα baseβ reviewα reviewβ grounding es =
    posterior-base-offset (baseα + reviewα) grounding es

  grounding-preserves-negative-mass : ∀ baseα baseβ reviewα reviewβ g₁ g₂ es →
    B.Beta.β (recompute baseα baseβ reviewα reviewβ g₁ es) ≡
    B.Beta.β (recompute baseα baseβ reviewα reviewβ g₂ es)
  grounding-preserves-negative-mass baseα baseβ reviewα reviewβ g₁ g₂ es = refl
