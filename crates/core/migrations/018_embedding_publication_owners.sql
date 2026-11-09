-- #!migration
-- name: "embedding-publication-owners",
-- description: "Revoke prepared work atomically with project deletion or explicit cancellation.",
-- requires: "candidate-key-content";

CREATE TABLE mimir_embedding_owners (
    owner_token uuid PRIMARY KEY DEFAULT gen_random_uuid(),
    project text,
    reserved_at timestamptz NOT NULL DEFAULT now(),
    operation_token uuid REFERENCES mimir_operation_reservations(operation_token)
);

CREATE FUNCTION mimir_embedding_owner_changed() RETURNS trigger
LANGUAGE plpgsql AS $$
BEGIN
    PERFORM pg_notify('mimir_embedding_owners_changed', '');
    RETURN NULL;
END;
$$;

CREATE TRIGGER mimir_embedding_owner_deleted
AFTER DELETE ON mimir_embedding_owners
FOR EACH STATEMENT EXECUTE FUNCTION mimir_embedding_owner_changed();
