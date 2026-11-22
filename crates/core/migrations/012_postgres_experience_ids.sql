-- #!migration
-- name: "postgres-experience-ids",
-- description: "Allocate experience UUIDs in PostgreSQL.",
-- requires: "review-work-events";
ALTER TABLE mimir_experiences ALTER COLUMN id SET DEFAULT gen_random_uuid();
