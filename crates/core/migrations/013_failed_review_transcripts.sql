-- #!migration
-- name: "failed-review-transcripts",
-- description: "Store unresolved review transcripts in PostgreSQL.",
-- requires: "postgres-experience-ids";
CREATE TABLE mimir_failed_review_transcripts (
    id uuid PRIMARY KEY DEFAULT gen_random_uuid(),
    attempt_key text NOT NULL UNIQUE,
    experience_id uuid NOT NULL,
    source_revision bigint NOT NULL,
    transcript jsonb NOT NULL,
    created_at timestamptz NOT NULL DEFAULT now(),
    FOREIGN KEY (experience_id, source_revision)
      REFERENCES mimir_experience_versions(experience_id, revision) ON DELETE CASCADE
);
CREATE INDEX mimir_failed_review_transcripts_source
    ON mimir_failed_review_transcripts(experience_id, source_revision);
