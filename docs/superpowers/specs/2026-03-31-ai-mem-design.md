# mimir Design Spec
*2026-03-31*

## What We're Building

A persistent belief graph for Claude Code sessions. The system captures how Claude builds, justifies, and revises its beliefs across conversations — not about external data (that's muninn), but about the quality and structure of Claude's own reasoning.

Primary consumer: Claude Code, via MCP tools.

## Core Concepts

**Non-monotonic probabilistic reasoning** (Judea Pearl + defeasible logic): beliefs carry probability scores, and a single defeater fact can cascade through the graph and revise the probability of everything downstream. This is the fundamental departure from flat key-value memory.

**Four goal properties:**
- (a) Causal chains — why Claude believes X (traceable justification graph)
- (b) Contradiction detection — two high-probability beliefs that cannot both be true trigger reconciliation
- (c) Confidence decay — belief probability decreases with time absent reinforcement
- (d) Relevance retrieval — "which beliefs are relevant to this context?" answered by graph traversal

## Architecture: Option B — AGE for Structure, Rust for Inference

```
Claude Code session
      │
      │ MCP tools (insert-belief, query-relevant, record-defeat, ...)
      ▼
 mimir-mcp  (MCP server, stdio)
      │
      │ typed Rust API
      ▼
 mimir-core  (Rust library)
      │  loads subgraph, runs inference, writes back scores
      ▼
 PostgreSQL + AGE  (same postgres-ai container)
      │
      └── AGE property graph (structural authority)
```

**AGE** owns the graph topology: which nodes exist, which edges connect them, what the current probability and weight values are. It is the durable, queryable memory substrate.

**mimir-core** owns computation: it loads the relevant subgraph into Rust data structures, runs defeasible propagation, and writes updated scores back. No inference logic in Cypher.

**mimir-mcp** is a thin MCP server that translates Claude's tool calls into mimir-core API calls.

## Graph Model

### Node types

| Type | Key fields |
|------|-----------|
| `Belief` | `id: UUID`, `content: Text`, `probability: f64 ∈ [0,1]`, `confidence: f64 ∈ [0,1]`, `created_at: Timestamp`, `last_activated_at: Timestamp` |
| `Pattern` | `id: UUID`, `situation: Text`, `approach: Text`, `activation_count: u32`, `success_rate: f64 ∈ [0,1]`, `created_at: DateTime<Utc>` |

### Edge types (all carry `weight: f64 ∈ [0,1]`)

| Type | Direction | Semantics |
|------|-----------|-----------|
| `SUPPORTS` | X → Y | X raises P(Y); weight = strength |
| `DEFEATS` | X → Y | X is a defeater for Y; triggers re-propagation of Y's downstream subgraph |
| `CAUSES` | X → Y | Pearl causal edge; X is a structural cause of Y |
| `CONTRADICTS` | X ↔ Y | Symmetric; when P(X) and P(Y) are both high, inference engine reconciles |

### Defeasibility invariant

`CONTRADICTS` edges are always bidirectional: if edge (X → Y) of type CONTRADICTS exists, edge (Y → X) must also exist. This is enforced at the Rust API layer, not left to callers.

### Probability invariant

All `probability` and `confidence` fields are bounded in [0, 1]. The Rust API returns `Err` on any value outside this range. The Agda spec states this as a type bound.

## Inference Engine (mimir-core)

**Defeasible propagation** — when a `DEFEATS(N → Y, weight w)` edge is inserted:

1. Load the subgraph reachable from Y via `SUPPORTS` and `CAUSES` edges.
2. Apply defeat attenuation: `P(Y) ← P(Y) × (1 - w × P(N))` — N's probability attenuates Y's.
3. Apply support boost for SUPPORTS edges: `P(Y) ← P(Y) + (1 − P(Y)) × w × P(X)`   [SUPPORTS: X supports Y with weight w]
4. Propagate downstream: for each node Z reachable from Y, recompute P(Z) based on its incoming `SUPPORTS`/`DEFEATS` edges.
5. Write updated scores back to AGE.

Non-monotonicity holds: there is no operation that prevents this cascade. A sufficiently strong defeater with high P(N) can collapse P(Y) to near zero regardless of prior support.

**CAUSES edges** — during defeasible propagation, `CAUSES` edges receive the same support boost as `SUPPORTS` edges: `P(Y) ← P(Y) + (1 − P(Y)) × w × P(X)`. The only difference between `SUPPORTS` and `CAUSES` is semantic (structural causal vs. evidential support); the propagation formula is identical.

**Contradiction reconciliation** — when two contradicting beliefs X, Y have P(X) + P(Y) > 1.0 + ε:

1. The inference engine reports the contradiction to the caller (does not silently resolve).
2. Claude Code decides which belief to attenuate or which new evidence to insert.

**Confidence decay** — on each session start, for each belief not activated in the last T days, apply: `confidence ← confidence × decay_factor^(days_since_activation)`. `decay_factor` and `T` are configurable.

## Agda Spec Scope (Phase 1)

The Agda spec defines the *behavioral contracts* of the Rust API, not graph-theoretic proofs. Specifically:

- `Belief` and `Pattern` record types with probability bounds stated as type constraints
- Type signatures for core operations: `insertBelief`, `insertEdge`, `recordDefeat`, `propagate`, `queryRelevant`, `decayAll`
- Stated (but not yet proven) invariants:
  - `CONTRADICTS` symmetry
  - probability ∈ [0,1] preservation through propagation
  - defeat propagation terminates (acyclic causal subgraph assumption)

The spec grows stricter as the implementation matures. Phase 1 is executable documentation that type-checks.

## Components

```
mimir/
├── spec/               # Agda spec
│   └── Mimir.agda
├── crates/
│   ├── core/           # mimir-core: typed API + inference engine
│   │   ├── src/
│   │   │   ├── lib.rs
│   │   │   ├── graph.rs      # Rust graph types (Belief, Pattern, Edge)
│   │   │   ├── store.rs      # AGE read/write via sqlx
│   │   │   ├── inference.rs  # defeasible propagation, decay
│   │   │   └── db.rs         # connection pool setup
│   │   └── Cargo.toml
│   └── mcp/            # mimir-mcp: MCP server (stdio)
│       ├── src/
│       │   └── main.rs
│       └── Cargo.toml
├── mimir-setup/
│   └── 01-setup.sh     # AGE graph init (docker exec, like muninn)
├── Cargo.toml          # workspace
└── muninn.toml         # (if mimir itself gets indexed by muninn)
```

## MCP Tools (Phase 1)

| Tool | Args | Effect |
|------|------|--------|
| `insert_belief` | `content, probability, confidence` | Add Belief node |
| `insert_pattern` | `situation, approach, success_rate` | Add Pattern node |
| `record_support` | `from_id, to_id, weight` | Add SUPPORTS edge + propagate |
| `record_defeat` | `from_id, to_id, weight` | Add DEFEATS edge + propagate cascade |
| `record_contradiction` | `id_a, id_b, weight?` (default 1.0) | Add CONTRADICTS pair |
| `query_relevant` | `context: Text, limit: u32` | Hybrid text+graph retrieval: matches beliefs by content substring, then expands to graph-adjacent beliefs reachable via SUPPORTS/CAUSES. Results ordered by probability descending. Vector/semantic search is a planned Phase 2 enhancement. |
| `get_contradictions` | — | List currently unresolved contradictions |
| `decay_all` | `decay_factor?` (default 0.99) | Apply confidence decay (called at session start) |
| `get_belief` | `id: string` | Fetch a belief by UUID |
| `list_beliefs` | — | List all beliefs |
| `list_patterns` | — | List all patterns |
| `propagate_from` | `id: string` | Manually trigger defeat propagation from a seed belief |
| `update_confidence` | `id: string, confidence: number` | Update the confidence of a belief |

## Testing

- Unit tests on inference.rs: propagation, defeat cascade, decay
- Integration tests against real AGE (same postgres-ai container pattern as muninn)
- Property-based tests (proptest): probability invariant holds through arbitrary sequences of insertions and defeats
- Agda spec type-checks as CI gate

## Out of Scope (Phase 1)

- Learning from feedback (automatic P update from Claude's success/failure signals) — Phase 2
- Cross-session belief merging / conflict resolution policy — Phase 2
- Agda proofs (only stated invariants, not proven) — future