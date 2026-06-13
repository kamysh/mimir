-- #!migration
-- name: "evidence-edges",
-- description: "Evidence edge: a DocumentChunk GROUNDS a Belief. GROUNDS is deliberately NOT a belief-edge label (not in EdgeType, not in SUPPORTS/DEFEATS/CAUSES/CONTRADICTS). It originates at a DocumentChunk and is never matched by belief↔belief traversal (get_downstream_beliefs, get_edges_among), so it cannot perturb inference. See Mimir.Evidence (propagate-evidence-invariant) for the formal non-interference guarantee. Idempotent: create_elabel is a no-op if the label already exists.",
-- requires: "belief-embeddings";
DO $$ BEGIN PERFORM ag_catalog.create_elabel(current_database()::text, 'GROUNDS'); EXCEPTION WHEN others THEN NULL; END $$;
