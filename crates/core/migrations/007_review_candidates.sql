-- #!migration
-- name: "review-candidates",
-- description: "Stable, experience-owned belief and pattern candidates with retained identity after review retraction or explicit node deletion.",
-- requires: "learning-ledger";
ALTER TABLE mimir_review_versions ADD COLUMN request jsonb;
CREATE TABLE mimir_review_candidates (
    experience_id uuid NOT NULL REFERENCES mimir_experiences(id) ON DELETE CASCADE,
    candidate_key text NOT NULL CHECK (length(candidate_key) BETWEEN 1 AND 128),
    kind text NOT NULL CHECK (kind IN ('belief', 'pattern')),
    node_id uuid NOT NULL UNIQUE,
    declaration jsonb NOT NULL,
    retired boolean NOT NULL DEFAULT false,
    PRIMARY KEY (experience_id, candidate_key)
);
CREATE INDEX mimir_review_candidates_node ON mimir_review_candidates(node_id);
