{-# OPTIONS --safe #-}
module Mimir.Types where

open import Data.Nat    using (ℕ)
open import Data.String using (String)
open import Data.Maybe  using (Maybe)

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
-- Timestamps are modelled as ℕ (Unix seconds).  The implementation uses
-- chrono::DateTime<Utc>; the correspondence is exact up to representation.
-- Belief::new() sets created_at = last_activated_at = Utc::now(), so for a
-- freshly created belief, createdAt b ≡ lastActivatedAt b holds at birth.
--
-- IMMUTABLE TIMESTAMPS: Both created_at and last_activated_at are write-once.
-- No API (MCP or internal service) modifies them after construction.
-- Consequence: decay runs continuously from birth with no reset mechanism.
-- The decay clock can never be reset — a long-lived belief accumulates
-- decay indefinitely until confidence reaches zero.
-- (update_confidence can manually restore confidence after decay, but
-- last_activated_at itself remains frozen.)
-- NOT YET MODELED: this record predates Phase 3 (Beta-belief posteriors,
-- alpha/beta/alpha0/beta0 in graph.rs) and the `memory_type` field
-- (Fact/Experiential/Working, graph.rs `MemoryType`) added after it — both
-- are real Rust-side fields this spec does not yet track. `memory_type`
-- gates `decay_all` (only Fact decays) and `query_relevant` (Working is
-- excluded from cross-session retrieval); it does not affect any proven
-- invariant here (non-interference, propagation order-independence, etc.),
-- so its omission does not invalidate the existing proofs — it is simply
-- undocumented in Agda, same status as the alpha/beta fields already are.
record Belief : Set where
  constructor mkBelief
  field
    id                : NodeId
    content           : String       -- text of the belief claim
    probability       : Prob
    confidence        : Prob
    createdAt         : ℕ            -- Unix timestamp (seconds); write-once
    lastActivatedAt   : ℕ            -- Unix timestamp (seconds); write-once; drives decay
    project           : Maybe String -- optional project scope for bulk-delete

-- ---------------------------------------------------------------------------
-- Pattern
-- Corresponds to the Rust `Pattern` struct in graph.rs.
-- Recurring situation/approach pairs; stored as AGE vertices separate from
-- beliefs.  Patterns have no edges to beliefs; they are retrieved by
-- semantic similarity only.
-- ---------------------------------------------------------------------------

-- Pattern::new() sets activation_count = 0.  The MCP `insert_pattern` tool
-- does not expose activation_count — it is always zero on creation.
--
-- IMMUTABILITY: There is NO API (MCP or internal service) to modify a
-- Pattern after creation.  Both `activationCount` and `successRate` are
-- write-once: set on creation, never updated.  `activationCount` is
-- semantically intended to track usage but currently has no increment
-- mechanism.  `delete_pattern` removes the entire vertex; there is no
-- partial-update path.  Patterns are effectively immutable records.
record Pattern : Set where
  constructor mkPattern
  field
    patId           : NodeId
    situation       : String    -- description of when this pattern applies
    approach        : String    -- recommended response / action
    activationCount : ℕ         -- intended usage counter; always 0 (no increment API)
    successRate     : Prob       -- empirical success rate; write-once at creation
    createdAt       : ℕ         -- Unix timestamp (seconds); mirrors Belief.createdAt
    project         : Maybe String -- optional project scope; bulk-deleted by delete_project
