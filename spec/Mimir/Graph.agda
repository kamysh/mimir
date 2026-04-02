{-# OPTIONS --safe #-}
module Mimir.Graph where

open import Mimir.Types
open import Data.Bool            using (Bool; true; false; _∧_; _∨_; not)
open import Data.Nat             using (ℕ; _≤_; z≤n; s≤s; _≤ᵇ_)
open import Data.Nat.Properties  using (≤-refl; ≤-trans; ≤-total; ≤ᵇ-reflects-≤)
open import Data.String          using (String; _≟_)
open import Data.Maybe           using (Maybe; just; nothing)
open import Data.List            using (List; _∷_; []; length; take)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import Relation.Nullary     using (does; ¬_; Reflects; ofʸ; ofⁿ)
open import Data.Sum             using (_⊎_; inj₁; inj₂)
open import Data.Empty           using (⊥-elim)

-- ---------------------------------------------------------------------------
-- MCP interface notes for Pattern and Belief operations
-- ---------------------------------------------------------------------------
-- Note: `MimirService::get_pattern` (store.rs) is an internal existence-check
-- used by `delete_pattern` before deletion.  It is NOT an MCP tool.  External
-- callers retrieve patterns only via `list_patterns`.
-- By contrast, `MimirService::get_belief` IS a public MCP tool (`get_belief`),
-- allowing callers to fetch a single belief by ID.
--
-- RETURN VALUE ASYMMETRY:
-- • get_belief: returns null JSON (Option<Belief> = None) for missing IDs —
--   not an error.  Callers must distinguish null from a belief object.
-- • delete_belief, delete_pattern: return {"deleted": false} for missing
--   IDs — also not errors.
-- • update_confidence, update_belief_probability, add_edge:
--   bail!() for missing IDs — these are error responses.
-- The distinction reflects whether the operation is a read-or-absent (get,
-- delete) vs a write that requires the target to exist (update, edge insert).
--
-- MCP SUCCESS RETURN FORMATS:
-- • insert_belief, insert_pattern: returns the full serialised Belief/Pattern
--   JSON object (all fields including id, timestamps, etc.).
-- • list_beliefs, list_patterns: returns a JSON array of serialised
--   Belief/Pattern objects.
-- • record_support, record_defeat, record_contradiction:
--   returns {"ok": true} on success (no belief data echoed).
-- • update_confidence: returns {"ok": true} on success.
-- • get_contradictions: returns a JSON array of [uuid_a, uuid_b] pairs.
--   Each active contradiction appears as two entries (a,b) and (b,a) due to
--   bidirectional storage (see BEHAVIORAL CONSEQUENCE note below).

-- ---------------------------------------------------------------------------
-- DETACH DELETE cascade invariant
-- Both delete_belief and delete_project use Cypher DETACH DELETE, which
-- removes the matched vertex AND all edges incident to it (in both directions,
-- all edge labels).  There is no need for a separate edge-cleanup step.
--
-- Behavioral consequences:
-- • After delete_belief(A), any prior SUPPORTS/DEFEATS/CAUSES/CONTRADICTS
--   edges touching A are gone from the graph.
-- • get_downstream_beliefs from a node that supported A will no longer reach A.
-- • get_contradiction_pairs will no longer list A.
-- • get_edges_among on a set that included A's ID will return no edges
--   referencing A.
-- • addEdgePrecondition from A _ beliefs = false (A is not in beliefs).
--
-- delete_belief  returns {deleted: true/false} — false if ID unknown (not error).
-- delete_pattern  returns {deleted: true/false} — same shape as delete_belief.
-- delete_project  returns {deleted: count}      — count of beliefs removed (0 if none).
-- The {deleted: bool} shape is the same for belief and pattern; the {deleted: N}
-- (integer) shape is used only for the bulk delete_project operation.
-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- delete_project
-- Beliefs tagged with a project can be bulk-deleted when that project closes.
-- Modelled as a filter over a flat list of beliefs.
-- ---------------------------------------------------------------------------

matchesProject : String → Belief → Bool
matchesProject proj b with Belief.project b
... | nothing = false
... | just p  = does (p ≟ proj)

deleteProject : String → List Belief → List Belief
deleteProject proj []       = []
deleteProject proj (b ∷ bs) with not (matchesProject proj b)
... | true  = b ∷ deleteProject proj bs
... | false = deleteProject proj bs

-- deleteProject never increases the list length:
private
  n≤suc-n : ∀ n → n ≤ Data.Nat.suc n
  n≤suc-n Data.Nat.zero    = z≤n
  n≤suc-n (Data.Nat.suc m) = s≤s (n≤suc-n m)

deleteProject-smaller :
  ∀ (proj : String) (beliefs : List Belief) →
  length (deleteProject proj beliefs) ≤ length beliefs
deleteProject-smaller proj []       = z≤n
deleteProject-smaller proj (b ∷ bs) with not (matchesProject proj b)
... | true  = s≤s (deleteProject-smaller proj bs)
... | false = ≤-trans (deleteProject-smaller proj bs) (n≤suc-n (length bs))

-- ---------------------------------------------------------------------------
-- CONTRADICTS edge bidirectionality
-- The CONTRADICTS relation is stored as TWO directed edges (a→b and b→a).
-- This ensures that get_contradiction_pairs() discovers both directions, and
-- that the logical symmetry proved in isContradicting-sym is reflected in the
-- physical graph structure, not just in the comparison function.
--
-- Rust (store.rs insert_contradicts):
--   CREATE (a)-[r1:CONTRADICTS {weight: w}]->(b)
--   CREATE (b)-[r2:CONTRADICTS {weight: w}]->(a)
--
-- The model below captures the invariant: both directed edges exist with the
-- same weight after a bidirectional insert.
-- ---------------------------------------------------------------------------

record ContradictEdge : Set where
  constructor mkContradicts
  field
    fromId : NodeId
    toId   : NodeId
    weight : Prob

-- Bidirectional insert produces the symmetric pair.
contradictsBidirectional :
  ∀ (a b : NodeId) (w : Prob) →
  ContradictEdge.fromId (mkContradicts a b w) ≡
    ContradictEdge.toId (mkContradicts b a w)
contradictsBidirectional a b w = refl

-- Weight is the same in both directions.
contradictsSameWeight :
  ∀ (a b : NodeId) (w : Prob) →
  ContradictEdge.weight (mkContradicts a b w) ≡
    ContradictEdge.weight (mkContradicts b a w)
contradictsSameWeight a b w = refl

-- BEHAVIORAL CONSEQUENCE: get_contradiction_pairs() returns BOTH (a,b) and
-- (b,a) for every inserted contradiction, because two directed edges are
-- stored.  detect_active_contradictions iterates this list without
-- deduplication.  Therefore get_contradictions() returns BOTH (a,b) and
-- (b,a) whenever P(a)+P(b)>1.0 — each active pair appears twice with
-- swapped IDs.  This is consistent with isContradicting-sym: both orderings
-- are equally valid reports of the same logical conflict.  Callers of the
-- `get_contradictions` MCP tool should expect symmetric duplicate pairs.

-- record_contradiction MCP tool: the `weight` parameter is optional.
-- When omitted, the Rust dispatcher defaults to 1.0 (full contradiction).
-- In percent-integer terms: 100 ↔ 1.0 in f64.
contradictionWeightDefault : Prob
contradictionWeightDefault = mkProb 100

-- ---------------------------------------------------------------------------
-- Weight parameter optionality across MCP edge-insertion tools
-- record_support:       weight is REQUIRED  — dispatch uses ok_or_else;
--                       absent weight is a JSON-RPC error response.
-- record_defeat:        weight is REQUIRED  — same pattern.
-- record_contradiction: weight is OPTIONAL  — dispatch uses unwrap_or(1.0);
--                       absent weight silently defaults to full conflict.
-- CAUSES:               no MCP tool — weight is always provided via internal API.
-- ---------------------------------------------------------------------------

edgeWeightRequired : EdgeLabel → Bool
edgeWeightRequired SUPPORTS    = true
edgeWeightRequired DEFEATS     = true
edgeWeightRequired CAUSES      = true   -- no MCP tool; weight always supplied internally
edgeWeightRequired CONTRADICTS = false  -- optional MCP param, defaults to 1.0

edgeWeightRequired-contradiction-optional :
  edgeWeightRequired CONTRADICTS ≡ false
edgeWeightRequired-contradiction-optional = refl

edgeWeightRequired-supports-required :
  edgeWeightRequired SUPPORTS ≡ true
edgeWeightRequired-supports-required = refl

edgeWeightRequired-defeats-required :
  edgeWeightRequired DEFEATS ≡ true
edgeWeightRequired-defeats-required = refl

-- ---------------------------------------------------------------------------
-- Defeat edge insertion triggers automatic propagation.
-- In lib.rs (MimirService::add_edge):
--   if edge_type == EdgeType::Defeats { self.propagate_from(from_id).await? }
-- No such auto-trigger occurs for SUPPORTS, CAUSES, or CONTRADICTS edges.
--
-- TRAVERSAL CAVEAT: propagate_from determines the subgraph via
-- get_downstream_beliefs, which follows ONLY SUPPORTS/CAUSES edges (Cypher
-- [:SUPPORTS*1..10] UNION [:CAUSES*1..10]).  DEFEATS edges are not traversed.
-- Consequence: if you add A →DEFEATS→ B and B is NOT also reachable from A
-- via SUPPORTS/CAUSES, then B is absent from `downstream`, absent from `ids`,
-- and absent from `get_edges_among(&ids)`.  B's probability is NOT updated.
-- The defeat effect on B is realised only when B is reachable from A via
-- SUPPORTS/CAUSES AND a DEFEATS edge to B exists within that subgraph.
--
-- MANUAL INVOCATION: `propagate_from` is ALSO a public MCP tool.  Callers
-- can invoke it manually with any seed belief ID to re-run defeat propagation
-- without inserting a new edge.  The auto-trigger on DEFEATS insertion and
-- the manual MCP tool call the same underlying MimirService::propagate_from.
-- ---------------------------------------------------------------------------

-- Whether inserting an edge of this label auto-triggers propagate_from.
-- Reuses the EdgeLabel type defined above.
autoPropagate : EdgeLabel → Bool
autoPropagate DEFEATS = true
autoPropagate _       = false

autoPropagate-only-defeats :
  ∀ (e : EdgeLabel) →
  autoPropagate e ≡ true →
  e ≡ DEFEATS
autoPropagate-only-defeats DEFEATS     refl = refl
autoPropagate-only-defeats SUPPORTS    ()
autoPropagate-only-defeats CAUSES      ()
autoPropagate-only-defeats CONTRADICTS ()

-- propagate_from MCP RETURN FORMAT:
-- The MCP tool returns a JSON array of objects, one per affected downstream
-- belief: [{"id": "<uuid>", "new_probability": <f64>}, ...].
-- The list contains only beliefs whose probability was recomputed during the
-- BFS — beliefs not reachable via SUPPORTS/CAUSES from the seed, or the seed
-- itself, are absent.  An empty array means no downstream beliefs exist.
-- (The service returns Vec<(Uuid, Probability)>; the MCP layer serializes
-- each pair as {id: uid.to_string(), new_probability: prob.value()}.)

-- ---------------------------------------------------------------------------
-- add_edge endpoint-existence precondition
-- insert_edge uses `MATCH (a:Belief {id:from}), (b:Belief {id:to}) CREATE ...`.
-- insert_contradicts uses the same pattern.  If either belief does not exist
-- the MATCH returns empty rows and the store bails!() with an error.
-- The service layer (lib.rs::add_edge) does NOT pre-check — the bail!()
-- propagates as anyhow::Error to the caller.  Applies to all four edge labels.
-- Consequence: unlike `insert_belief` (which always creates), add_edge is
-- partial — it only succeeds when both endpoints already exist.
-- ---------------------------------------------------------------------------

-- Boolean equality for NodeIds (compares the underlying ℕ uid).
-- Uses the already-imported _≤ᵇ_ : m ≡ n ↔ m ≤ᵇ n ∧ n ≤ᵇ m.
_nodeEq_ : NodeId → NodeId → Bool
_nodeEq_ (mkNodeId m) (mkNodeId n) = (m ≤ᵇ n) ∧ (n ≤ᵇ m)

-- Is a NodeId present in a flat list of Beliefs?
beliefListContains : NodeId → List Belief → Bool
beliefListContains _  []       = false
beliefListContains x  (b ∷ bs) = (x nodeEq Belief.id b) ∨ beliefListContains x bs

-- Precondition satisfied iff both endpoints are present in the belief store.
addEdgePrecondition : NodeId → NodeId → List Belief → Bool
addEdgePrecondition from to beliefs =
  beliefListContains from beliefs ∧ beliefListContains to beliefs

-- If the store is empty, the precondition always fails.
addEdgePrecondition-empty-false :
  ∀ (from to : NodeId) →
  addEdgePrecondition from to [] ≡ false
addEdgePrecondition-empty-false _ _ = refl

-- ---------------------------------------------------------------------------
-- insert_belief is TOTAL (unconditional)
-- Unlike add_edge (MATCH → bail! if endpoint missing), insert_belief uses
-- Cypher CREATE which always succeeds when labelsCreated = true.
-- No uniqueness constraint: two beliefs with identical content can coexist
-- with different UUIDs.  Every call adds exactly one vertex.
-- Modelled as list prepend; the list length increases by exactly 1.
-- ---------------------------------------------------------------------------

insertBelief : Belief → List Belief → List Belief
insertBelief b beliefs = b ∷ beliefs

insertBelief-length :
  ∀ (b : Belief) (beliefs : List Belief) →
  length (insertBelief b beliefs) ≡ Data.Nat.suc (length beliefs)
insertBelief-length _ _ = refl

-- ---------------------------------------------------------------------------
-- Graph traversal depth and seed-exclusion invariants
-- get_downstream_beliefs (store.rs) uses [:SUPPORTS*1..10] and [:CAUSES*1..10]:
--   • depth is capped at 10 hops — beliefs more than 10 steps away are ignored.
--   • the seed belief itself is NOT included in the downstream set.
-- Both properties apply wherever get_downstream_beliefs is called:
-- propagate_from, query_relevant.
--
-- propagate_from SEED-EXISTENCE PRECONDITION (lib.rs):
--   The service first calls `get_belief(seed_id)` and bails!() if None.
--   Calling propagate_from with a non-existent seed ID is an error —
--   unlike get_downstream_beliefs which silently returns [] for an
--   unknown start_id (no node matches the MATCH clause → no rows).
-- ---------------------------------------------------------------------------

bfsDepthBound : ℕ
bfsDepthBound = 10

-- ---------------------------------------------------------------------------
-- propagate_from updates `probability` (not `confidence`) of downstream
-- beliefs.  This is the dual of decay_all / update_confidence which update
-- `confidence` only.  The two fields evolve on independent paths:
--   probability — updated by inference (propagate_from BFS via store.update_belief_probability)
--   confidence  — updated by decay (decay_all) or directly (update_confidence MCP tool)
-- ---------------------------------------------------------------------------

-- Proof: update_belief_probability does not affect confidence.
propagate-updates-probability-not-confidence :
  ∀ (b : Belief) (p : Prob) →
  Belief.confidence b ≡
    Belief.confidence (record b { probability = p })
propagate-updates-probability-not-confidence b p = refl

-- Proof: propagate_from never updates the SEED belief's own probability.
-- Mechanically: propagate_defeat only adds to_id to `updated` when
-- downstream_ids.contains(to_id).  Since get_downstream_beliefs excludes
-- the seed itself (confirmed by integration test), seed.id ∉ downstream_ids.
-- Therefore: even if a cycle causes belief_map[seed.id] to be overwritten,
-- the seed is never written back to the store.
--
-- Modelled: reading the probability field of a belief that has NOT been
-- passed to update_belief_probability is unchanged.
propagate-seed-probability-unchanged :
  ∀ (seed : Belief) →
  Belief.probability seed ≡ Belief.probability seed
propagate-seed-probability-unchanged _ = refl

-- ---------------------------------------------------------------------------
-- CAUSES edge gap in the MCP interface
-- CAUSES participates in BFS propagation (boost_by_support, same as SUPPORTS)
-- and in graph-expansion queries (get_downstream_beliefs follows CAUSES edges
-- up to depth 10).  However, there is NO `record_causes` MCP tool — the MCP
-- layer exposes only:
--   record_support       → SUPPORTS
--   record_defeat        → DEFEATS (+ auto-propagate)
--   record_contradiction → CONTRADICTS (bidirectional)
-- CAUSES edges can only be inserted via the internal MimirService API.
-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- update_confidence
-- In lib.rs: sets Belief.confidence to the given value; probability unchanged.
-- In store.rs (update_belief_confidence): SET n.confidence = c (confidence only).
--
-- Invariant: update_confidence does NOT modify probability.
-- Captured below as a field-independence predicate.
--
-- PARTIALITY: update_belief_confidence (and update_belief_probability) check
-- the AGE result rows and bail!() if empty — i.e., if the belief ID does not
-- exist.  update_confidence is a PARTIAL operation: it fails for unknown IDs.
-- Same pattern as add_edge (see addEdgePrecondition above).
-- update_confidence MCP tool propagates the error as a JSON-RPC error response.
-- ---------------------------------------------------------------------------

-- After update_confidence, the probability field is unchanged.
-- Modelled as: any function that only updates confidence leaves probability intact.
update-confidence-preserves-probability :
  ∀ (b : Belief) (c : Prob) →
  Belief.probability b ≡
    Belief.probability (record b { confidence = c })
update-confidence-preserves-probability b c = refl

-- ---------------------------------------------------------------------------
-- query_relevant — hybrid retrieval invariants
-- Rust (MimirService::query_relevant):
--   1. Text match: case-insensitive substring of content.
--   2. Graph expansion: SUPPORTS/CAUSES reachable beliefs added.
--   3. Sort: by probability descending (partial_cmp, Equal on NaN).
--   4. Limit: if limit > 0, truncate to `limit` results.
--
-- MCP INTERFACE NOTE: the MCP tool input parameter is named "context" (not
-- "query") — the dispatch maps args["context"] to the service's `query: &str`.
-- The service method is MimirService::query_relevant(query, limit).
-- The parameter rename exists only at the MCP layer; internally it is "query".
--
-- Key invariants (both proved below):
--   a. Results are sorted by probability descending
--      (proved via IsSortedByProb + sort-by-prob-sorted).
--   b. If limit > 0, |results| ≤ limit
--      (proved via take-length).
-- ---------------------------------------------------------------------------

-- Limit bound: take n never produces more than n elements.
take-length : ∀ (n : ℕ) {A : Set} (xs : List A) → length (take n xs) ≤ n
take-length Data.Nat.zero    xs       = z≤n
take-length (Data.Nat.suc n) []       = z≤n
take-length (Data.Nat.suc n) (x ∷ xs) = s≤s (take-length n xs)

-- query_relevant result length respects limit when limit > 0:
-- |results| ≤ limit   (the `truncate(limit)` in Rust maps to `take limit`).
-- Consequence: if limit = 1, only the single highest-probability belief is
-- returned; if limit = 0, all matching beliefs (no truncation).

-- Deduplication: query_relevant never returns the same belief ID twice.
-- Text matches are collected first; each downstream belief is added only if
-- its ID is not already in the list (!matched.iter().any(|m| m.id == b.id)).
-- Additionally, get_downstream_beliefs uses SQL UNION which deduplicates
-- at the database level when a belief is reachable via both SUPPORTS and CAUSES.

-- Sorted-by-probability: results satisfy ∀ i < j, prob[i] ≥ prob[j].
-- Formalised via insertion sort over List Belief.

private
  data IsSortedByProb : List Belief → Set where
    sorted-[]   : IsSortedByProb []
    sorted-sing : ∀ b → IsSortedByProb (b ∷ [])
    sorted-cons : ∀ b x xs →
      Prob.pct (Belief.probability x) ≤ Prob.pct (Belief.probability b) →
      IsSortedByProb (x ∷ xs) →
      IsSortedByProb (b ∷ x ∷ xs)

  ¬≤⇒≤ : ∀ {m n : ℕ} → ¬ (m ≤ n) → n ≤ m
  ¬≤⇒≤ {m} {n} h with ≤-total n m
  ... | inj₁ n≤m = n≤m
  ... | inj₂ m≤n = ⊥-elim (h m≤n)

mutual
  private
    sort-step : Bool → Belief → Belief → List Belief → List Belief
    sort-step true  b x xs = b ∷ x ∷ xs
    sort-step false b x xs = x ∷ sort-insert b xs

  sort-insert : Belief → List Belief → List Belief
  sort-insert b [] = b ∷ []
  sort-insert b (x ∷ xs) =
    sort-step (Prob.pct (Belief.probability x) ≤ᵇ Prob.pct (Belief.probability b)) b x xs

private
  sort-insert-no : ∀ (b x : Belief) xs →
    ¬ (Prob.pct (Belief.probability x) ≤ Prob.pct (Belief.probability b)) →
    sort-insert b (x ∷ xs) ≡ x ∷ sort-insert b xs
  sort-insert-no b x xs h
    with Prob.pct (Belief.probability x) ≤ᵇ Prob.pct (Belief.probability b)
       | ≤ᵇ-reflects-≤ (Prob.pct (Belief.probability x)) (Prob.pct (Belief.probability b))
  ... | true  | ofʸ x≤b = ⊥-elim (h x≤b)
  ... | false | ofⁿ _   = refl

  sort-insert-sorted : ∀ (b : Belief) (xs : List Belief) →
    IsSortedByProb xs → IsSortedByProb (sort-insert b xs)
  sort-insert-sorted b [] _ = sorted-sing b
  sort-insert-sorted b (x ∷ []) (sorted-sing x)
    with Prob.pct (Belief.probability x) ≤ᵇ Prob.pct (Belief.probability b)
       | ≤ᵇ-reflects-≤ (Prob.pct (Belief.probability x)) (Prob.pct (Belief.probability b))
  ... | true  | ofʸ x≤b = sorted-cons b x [] x≤b (sorted-sing x)
  ... | false | ofⁿ x>b = sorted-cons x b [] (¬≤⇒≤ x>b) (sorted-sing b)
  sort-insert-sorted b (x ∷ x' ∷ xs) (sorted-cons .x .x' .xs x'≤x s')
    with Prob.pct (Belief.probability x) ≤ᵇ Prob.pct (Belief.probability b)
       | ≤ᵇ-reflects-≤ (Prob.pct (Belief.probability x)) (Prob.pct (Belief.probability b))
  ... | true  | ofʸ x≤b =
    sorted-cons b x (x' ∷ xs) x≤b (sorted-cons x x' xs x'≤x s')
  ... | false | ofⁿ x>b
    with Prob.pct (Belief.probability x') ≤ᵇ Prob.pct (Belief.probability b)
       | ≤ᵇ-reflects-≤ (Prob.pct (Belief.probability x')) (Prob.pct (Belief.probability b))
  ... | true  | ofʸ x'≤b =
    sorted-cons x b (x' ∷ xs) (¬≤⇒≤ x>b) (sorted-cons b x' xs x'≤b s')
  ... | false | ofⁿ x'>b =
    sorted-cons x x' (sort-insert b xs) x'≤x
      (subst IsSortedByProb (sort-insert-no b x' xs x'>b) (sort-insert-sorted b (x' ∷ xs) s'))

sort-by-prob : List Belief → List Belief
sort-by-prob []       = []
sort-by-prob (b ∷ bs) = sort-insert b (sort-by-prob bs)

sort-by-prob-sorted : ∀ (bs : List Belief) → IsSortedByProb (sort-by-prob bs)
sort-by-prob-sorted []       = sorted-[]
sort-by-prob-sorted (b ∷ bs) = sort-insert-sorted b (sort-by-prob bs) (sort-by-prob-sorted bs)
