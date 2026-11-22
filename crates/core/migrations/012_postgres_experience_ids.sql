-- #!migration
-- name: "postgres-experience-ids",
-- description: "Allocate experience UUIDs in PostgreSQL and retain creation request keys.",
-- requires: "review-work-events";
ALTER TABLE mimir_experiences
    ALTER COLUMN id SET DEFAULT gen_random_uuid(),
    ADD COLUMN creation_request_key uuid,
    ADD CONSTRAINT mimir_experiences_creation_request_key UNIQUE (creation_request_key);
