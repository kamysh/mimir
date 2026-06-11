{-# OPTIONS --safe #-}
-- Top-level re-export module.
-- Import this for access to the full Mimir spec in one open.
-- Import individual submodules for targeted access:
--   Mimir.Types     — core data types (Prob, NodeId, Belief, Pattern, …)
--   Mimir.Inference — inference engine (attenuate, decay, boost, proofs)
--   Mimir.Graph     — graph operations (edges, BFS, sort, MCP semantics)
--   Mimir.Beta      — Phase 3: beliefs as Beta(α,β) (mean monotonicity, idempotence)
module Mimir where

open import Mimir.Types     public
open import Mimir.Inference public
open import Mimir.Graph     public
open import Mimir.Documents public
open import Mimir.Evidence  public
open import Mimir.Beta      public
