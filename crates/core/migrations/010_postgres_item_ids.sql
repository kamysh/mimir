-- #!migration
-- name: "postgres-item-allocation",
-- description: "Allocate learning item UUIDs in PostgreSQL using experience-local keys, preserving historical identities.",
-- requires: "learning-item-owners";

-- Historical UUIDs are imported, never regenerated. Existing ownership rows
-- remain authoritative if an older history contains conflicting provenance.
INSERT INTO mimir_learning_item_owners(item_id,experience_id,source_ref,actor)
SELECT (item->>'id')::uuid, experience_id, item->>'source_ref', item->>'actor'
FROM (
    SELECT experience_id, jsonb_array_elements(COALESCE(payload->'learning_items','[]'::jsonb)) AS item
    FROM mimir_experience_versions
    UNION ALL
    SELECT experience_id, jsonb_array_elements(COALESCE(payload->'extracted_items','[]'::jsonb)) AS item
    FROM mimir_review_versions
) AS historical
ON CONFLICT(item_id) DO NOTHING;

ALTER TABLE mimir_learning_item_owners
    ALTER COLUMN item_id SET DEFAULT gen_random_uuid(),
    ADD COLUMN item_key text,
    ADD CONSTRAINT mimir_learning_item_local_key UNIQUE(experience_id,item_key),
    ADD CONSTRAINT mimir_learning_item_key_nonempty CHECK(item_key IS NULL OR length(btrim(item_key)) > 0);
