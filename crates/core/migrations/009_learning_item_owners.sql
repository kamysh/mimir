-- #!migration
-- name: "learning-item-owners",
-- description: "Reserve stable item identities and their source provenance across experience corrections.",
-- requires: "learning-assessments";
CREATE TABLE mimir_learning_item_owners (
    item_id uuid PRIMARY KEY,
    experience_id uuid NOT NULL REFERENCES mimir_experiences(id) ON DELETE CASCADE,
    source_ref text NOT NULL,
    actor text NOT NULL
);
