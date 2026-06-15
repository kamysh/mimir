{-# OPTIONS --safe #-}
-- ---------------------------------------------------------------------------
-- Mimir.Evidence — document-grounded beliefs (Phase 4 C-core).
--
-- A DocumentChunk grounds a Belief via a GROUNDS edge. The hard invariant is
-- NON-INTERFERENCE: the evidence overlay must not perturb belief↔belief
-- inference. This module formalises that guarantee.
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
open import Mimir.Documents using (Embedding)
open import Data.Bool       using (Bool; true; false; _∧_)
open import Data.List       using (List; []; _∷_; _++_)
open import Data.Maybe      using (Maybe; just; nothing)
open import Data.String     using (String; _≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (does)

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
-- proofs (whatever propagation actually computes) are preserved verbatim.
propagate-evidence-invariant :
  ∀ {A : Set} (propagate : List Edge → A)
    (es : List EvidenceEdge) (g : Graph) →
  propagate (inferenceSubstrate (overlay es g)) ≡ propagate (inferenceSubstrate g)
propagate-evidence-invariant propagate es g =
  cong propagate (overlay-preserves-substrate es g)

-- ---------------------------------------------------------------------------
-- Auto-grounding — GROUNDS edges created automatically at load_document and
-- insert_belief time, rather than only via explicit add_evidence calls.
--
-- CREATION PATHS for GROUNDS edges:
--   1. Manual:    add_evidence(chunk_id, belief_id, weight) — explicit call.
--   2. Automatic: load_document — for each new chunk, find beliefs whose
--                 stored embedding is within GROUND_THRESHOLD cosine similarity
--                 of the chunk embedding; create one EvidenceEdge per match.
--   3. Automatic: insert_belief — for each new belief, find chunks whose
--                 stored embedding is within GROUND_THRESHOLD cosine similarity
--                 of the belief embedding; create one EvidenceEdge per match.
--
-- PROJECT SCOPING RULE (both auto paths):
--   A chunk c and belief b are eligible for auto-grounding iff:
--     chunk.project = belief.project  (same project), OR
--     chunk.project = nothing          (global chunk, grounds any belief), OR
--     belief.project = nothing         (global belief, grounded by any chunk).
--   This mirrors query_document's project-scoping logic.
--
-- NON-INTERFERENCE is preserved: all three paths produce only EvidenceEdges,
-- never belief-graph Edges. The propagate-evidence-invariant theorem above
-- holds unconditionally for auto-grounded edges — the proof is identical.
-- ---------------------------------------------------------------------------

-- Project compatibility: chunk and belief may be auto-grounded together iff
-- at least one of their project fields is nothing, or both are the same project.
projectCompatible : Maybe String → Maybe String → Bool
projectCompatible nothing  _        = true
projectCompatible _        nothing  = true
projectCompatible (just p) (just q) = does (p ≟ q)

-- A grounding entry: a node id, its embedding vector, and its project tag.
-- Used for both chunk and belief sides of auto-grounding.
-- Named GroundingEntry to avoid clashing with Documents.EmbeddingEntry
-- (which lacks the project field).
record GroundingEntry : Set where
  constructor mkGroundingEntry
  field
    geNodeId    : NodeId
    geEmbedding : Embedding
    geProject   : Maybe String

-- similarEnough is not expressible in --safe Agda (requires real arithmetic).
-- It is threaded as a parameter so callers supply the concrete predicate
-- (the Rust implementation uses 1 − cosine_distance ≥ GROUND_THRESHOLD = 0.80).

-- autoGroundChunk: given one chunk (id, embedding, project), a similarity
-- predicate, and a list of belief grounding entries, produce GROUNDS edges
-- for all beliefs that are project-compatible and similar enough.
-- The Rust side passes the actual cosine similarity score as weight; here we
-- use a unit Prob (80) as a placeholder not expressible in safe Agda.
autoGroundChunk : (Embedding → Embedding → Bool)
                → NodeId → Embedding → Maybe String
                → List GroundingEntry
                → List EvidenceEdge
autoGroundChunk _   _       _        _         []  = []
autoGroundChunk sim chunkId chunkEmb chunkProj (mkGroundingEntry bId bEmb bProj ∷ bs) with
    sim chunkEmb bEmb ∧ projectCompatible chunkProj bProj
... | false = autoGroundChunk sim chunkId chunkEmb chunkProj bs
... | true  = mkEvidence chunkId bId (mkProb 80)
            ∷ autoGroundChunk sim chunkId chunkEmb chunkProj bs

-- autoGroundChunks: run autoGroundChunk for every new chunk. Called at the
-- end of load_document after all chunk embeddings are stored.
autoGroundChunks : (Embedding → Embedding → Bool)
                 → List GroundingEntry   -- new chunks
                 → List GroundingEntry   -- existing belief embeddings
                 → List EvidenceEdge
autoGroundChunks _   []  _       = []
autoGroundChunks sim (mkGroundingEntry cId cEmb cProj ∷ cs) beliefs =
  autoGroundChunk sim cId cEmb cProj beliefs
  ++ autoGroundChunks sim cs beliefs

-- autoGroundBelief: given one belief (id, embedding, project), a similarity
-- predicate, and a list of chunk grounding entries, produce GROUNDS edges
-- for all chunks that are project-compatible and similar enough.
-- Called at the end of insert_belief after the belief embedding is stored.
autoGroundBelief : (Embedding → Embedding → Bool)
                 → NodeId → Embedding → Maybe String
                 → List GroundingEntry
                 → List EvidenceEdge
autoGroundBelief _   _    _     _     []  = []
autoGroundBelief sim bId bEmb bProj (mkGroundingEntry cId cEmb cProj ∷ cs) with
    sim bEmb cEmb ∧ projectCompatible bProj cProj
... | false = autoGroundBelief sim bId bEmb bProj cs
... | true  = mkEvidence cId bId (mkProb 80)
            ∷ autoGroundBelief sim bId bEmb bProj cs

-- KEY INVARIANT: auto-grounding produces only EvidenceEdges.
-- The substrate (beliefEdges) of any Graph is unchanged by applying the
-- auto-grounded overlay — a direct corollary of propagate-evidence-invariant.
--
-- Proof: autoGroundChunks / autoGroundBelief return List EvidenceEdge;
-- overlay (auto-grounded edges) g = mkGraph (beliefEdges g) (...),
-- so inferenceSubstrate is unchanged. No additional lemma is needed beyond
-- propagate-evidence-invariant, which already quantifies over all overlays.
