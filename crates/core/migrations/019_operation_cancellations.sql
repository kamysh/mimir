-- #!migration
-- name: "operation-cancellations",
-- description: "Persist explicit cancellation, preserve saved answers, and block late operation publication.",
-- requires: "embedding-publication-owners";

CREATE TABLE mimir_operation_cancellations (
    operation_token uuid PRIMARY KEY REFERENCES mimir_operation_reservations(operation_token),
    cancelled_at timestamptz NOT NULL DEFAULT now()
);

CREATE FUNCTION mimir_require_active_operation() RETURNS trigger
LANGUAGE plpgsql AS $$
BEGIN
    IF NEW.operation_token IS NULL THEN
        RETURN NEW;
    END IF;
    PERFORM 1 FROM mimir_operation_reservations
        WHERE operation_token = NEW.operation_token FOR UPDATE;
    IF NOT FOUND THEN
        RAISE EXCEPTION 'Unknown operation token; recover its original reservation before writing'
            USING ERRCODE = '23514';
    END IF;
    IF EXISTS (SELECT 1 FROM mimir_operation_cancellations
               WHERE operation_token = NEW.operation_token) THEN
        RAISE EXCEPTION 'Operation % was explicitly cancelled; read its saved answers and cancellation record, then ask the user before starting different work', NEW.operation_token
            USING ERRCODE = '23514';
    END IF;
    RETURN NEW;
END;
$$;

CREATE TRIGGER mimir_binding_requires_active_operation
BEFORE INSERT ON mimir_operation_bindings
FOR EACH ROW EXECUTE FUNCTION mimir_require_active_operation();
CREATE TRIGGER mimir_plan_requires_active_operation
BEFORE INSERT ON mimir_operation_plans
FOR EACH ROW EXECUTE FUNCTION mimir_require_active_operation();
CREATE TRIGGER mimir_step_requires_active_operation
BEFORE INSERT ON mimir_operation_step_replies
FOR EACH ROW EXECUTE FUNCTION mimir_require_active_operation();
CREATE TRIGGER mimir_owner_requires_active_operation
BEFORE INSERT ON mimir_embedding_owners
FOR EACH ROW EXECUTE FUNCTION mimir_require_active_operation();

CREATE FUNCTION mimir_check_cancellation_publication() RETURNS trigger
LANGUAGE plpgsql AS $$
BEGIN
    PERFORM 1 FROM mimir_operation_reservations
        WHERE operation_token = NEW.operation_token FOR UPDATE;
    IF NOT FOUND THEN
        RAISE EXCEPTION 'Unknown operation token; recover its reservation before cancelling'
            USING ERRCODE = '23514';
    END IF;
    IF EXISTS (SELECT 1 FROM mimir_operation_step_replies
               WHERE operation_token = NEW.operation_token AND step = '@operation-result') THEN
        RAISE EXCEPTION 'This operation already has a saved result; read that original result instead of cancelling it'
            USING ERRCODE = '23514';
    END IF;
    RETURN NEW;
END;
$$;
CREATE TRIGGER mimir_cancellation_preserves_saved_result
BEFORE INSERT ON mimir_operation_cancellations
FOR EACH ROW EXECUTE FUNCTION mimir_check_cancellation_publication();

CREATE FUNCTION mimir_preserve_cancellation() RETURNS trigger
LANGUAGE plpgsql AS $$
BEGIN
    RAISE EXCEPTION 'Cancellation is immutable; read its original receipt and saved answers, then ask the user before starting different work'
        USING ERRCODE = '23514';
END;
$$;
CREATE TRIGGER mimir_cancellation_immutable
BEFORE UPDATE OR DELETE ON mimir_operation_cancellations
FOR EACH ROW EXECUTE FUNCTION mimir_preserve_cancellation();

CREATE FUNCTION mimir_preserve_preparation_operation() RETURNS trigger
LANGUAGE plpgsql AS $$
BEGIN
    IF NEW.operation_token IS DISTINCT FROM OLD.operation_token THEN
        RAISE EXCEPTION 'Preparation ownership cannot move to another operation; retain its original owner and ask the user before starting different work'
            USING ERRCODE = '23514';
    END IF;
    RETURN NEW;
END;
$$;
CREATE TRIGGER mimir_preparation_operation_immutable
BEFORE UPDATE OF operation_token ON mimir_embedding_owners
FOR EACH ROW EXECUTE FUNCTION mimir_preserve_preparation_operation();
