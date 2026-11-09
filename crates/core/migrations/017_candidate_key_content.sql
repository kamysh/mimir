-- #!migration
-- name: "candidate-key-content",
-- description: "Accept complete nonempty candidate keys without an application length ceiling.",
-- requires: "operation-request-keys";

ALTER TABLE mimir_review_candidates
    DROP CONSTRAINT mimir_review_candidates_candidate_key_check,
    ADD CONSTRAINT mimir_review_candidates_candidate_key_nonempty
        CHECK (length(candidate_key) > 0);
