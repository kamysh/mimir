-- #!migration
-- name: "operation-request-keys",
-- description: "Recover the original PostgreSQL reservation using a stable request key.",
-- requires: "operation-plans";

CREATE TABLE mimir_operation_request_keys (
    request_key text PRIMARY KEY CHECK (length(btrim(request_key)) > 0),
    operation_token uuid NOT NULL UNIQUE REFERENCES mimir_operation_reservations(operation_token)
);

CREATE FUNCTION mimir_preserve_operation_request_key() RETURNS trigger
LANGUAGE plpgsql AS $$
BEGIN
    RAISE EXCEPTION 'Request key is immutable; repeat the original key to recover its reservation'
        USING ERRCODE = '23514';
END;
$$;

CREATE TRIGGER mimir_operation_request_key_immutable
BEFORE UPDATE OR DELETE ON mimir_operation_request_keys
FOR EACH ROW EXECUTE FUNCTION mimir_preserve_operation_request_key();

CREATE FUNCTION mimir_preserve_keyed_reservation() RETURNS trigger
LANGUAGE plpgsql AS $$
BEGIN
    IF EXISTS (SELECT 1 FROM mimir_operation_request_keys WHERE operation_token = OLD.operation_token) THEN
        RAISE EXCEPTION 'Reservation is immutable; repeat its request key to recover the original token and time'
            USING ERRCODE = '23514';
    END IF;
    IF TG_OP = 'DELETE' THEN
        RETURN OLD;
    END IF;
    RETURN NEW;
END;
$$;

CREATE TRIGGER mimir_keyed_reservation_immutable
BEFORE UPDATE OR DELETE ON mimir_operation_reservations
FOR EACH ROW EXECUTE FUNCTION mimir_preserve_keyed_reservation();
