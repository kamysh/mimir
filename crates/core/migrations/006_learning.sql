-- #!migration
-- name: "learning-ledger",
-- description: "Versioned experiences and reviews. Source records are immutable; current pointers select active evidence and pending review work. No existing belief or pattern is rewritten by this migration.",
-- requires: "beta-beliefs";
CREATE TABLE mimir_experiences (
    id uuid PRIMARY KEY,
    project text NOT NULL,
    revision bigint NOT NULL CHECK (revision > 0),
    review_revision bigint NOT NULL DEFAULT 0,
    reviewed_revision bigint NOT NULL DEFAULT 0,
    updated_at timestamptz NOT NULL DEFAULT now()
);
CREATE TABLE mimir_experience_versions (
    experience_id uuid NOT NULL REFERENCES mimir_experiences(id) ON DELETE CASCADE,
    revision bigint NOT NULL,
    payload jsonb NOT NULL,
    created_at timestamptz NOT NULL DEFAULT now(),
    PRIMARY KEY (experience_id, revision)
);
CREATE TABLE mimir_review_versions (
    experience_id uuid NOT NULL REFERENCES mimir_experiences(id) ON DELETE CASCADE,
    revision bigint NOT NULL,
    experience_revision bigint NOT NULL,
    payload jsonb NOT NULL,
    created_at timestamptz NOT NULL DEFAULT now(),
    PRIMARY KEY (experience_id, revision),
    FOREIGN KEY (experience_id, experience_revision)
      REFERENCES mimir_experience_versions(experience_id, revision)
);
CREATE INDEX mimir_pending_reviews ON mimir_experiences(updated_at, id)
    WHERE reviewed_revision < revision;
