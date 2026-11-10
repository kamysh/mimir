-- #!migration
-- name: "operation-execution-stops",
-- description: "Retain every execution until its actual owner confirms physical cleanup.",
-- requires: "review-preparation-events";

CREATE TABLE mimir_operation_executions (
    execution_id uuid PRIMARY KEY DEFAULT gen_random_uuid(),
    operation_token uuid NOT NULL REFERENCES mimir_operation_reservations(operation_token),
    owner_program text NOT NULL,
    owner_pid bigint NOT NULL,
    owner_host text,
    owner_host_source text,
    client_address text DEFAULT inet_client_addr()::text,
    registered_at timestamptz NOT NULL DEFAULT clock_timestamp(),
    stopped_at timestamptz
);
CREATE INDEX mimir_operation_executions_pending
    ON mimir_operation_executions(operation_token) WHERE stopped_at IS NULL;

CREATE TRIGGER mimir_execution_requires_active_operation
BEFORE INSERT ON mimir_operation_executions
FOR EACH ROW EXECUTE FUNCTION mimir_require_active_operation();

CREATE FUNCTION mimir_execution_stop_only() RETURNS trigger
LANGUAGE plpgsql AS $$
BEGIN
    IF TG_OP = 'DELETE' THEN
        RAISE EXCEPTION 'Execution ownership cannot be deleted or expired; retain its actual stop acknowledgement';
    END IF;
    IF NEW.execution_id IS DISTINCT FROM OLD.execution_id
       OR NEW.operation_token IS DISTINCT FROM OLD.operation_token
       OR NEW.registered_at IS DISTINCT FROM OLD.registered_at
       OR NEW.owner_program IS DISTINCT FROM OLD.owner_program
       OR NEW.owner_pid IS DISTINCT FROM OLD.owner_pid
       OR NEW.owner_host IS DISTINCT FROM OLD.owner_host
       OR NEW.owner_host_source IS DISTINCT FROM OLD.owner_host_source
       OR NEW.client_address IS DISTINCT FROM OLD.client_address
       OR OLD.stopped_at IS NOT NULL
       OR NEW.stopped_at IS NULL THEN
        RAISE EXCEPTION 'Only the original execution owner may record its one physical-stop acknowledgement';
    END IF;
    RETURN NEW;
END;
$$;
CREATE TRIGGER mimir_execution_stop_immutable
BEFORE UPDATE OR DELETE ON mimir_operation_executions
FOR EACH ROW EXECUTE FUNCTION mimir_execution_stop_only();

CREATE FUNCTION mimir_execution_acknowledged() RETURNS trigger
LANGUAGE plpgsql AS $$
BEGIN
    PERFORM pg_notify('mimir_operation_execution_stopped', NEW.operation_token::text);
    RETURN NULL;
END;
$$;
CREATE TRIGGER mimir_execution_stop_changed
AFTER UPDATE ON mimir_operation_executions
FOR EACH ROW EXECUTE FUNCTION mimir_execution_acknowledged();

CREATE FUNCTION mimir_operation_cancelled() RETURNS trigger
LANGUAGE plpgsql AS $$
BEGIN
    PERFORM pg_notify('mimir_operation_cancelled', NEW.operation_token::text);
    RETURN NULL;
END;
$$;
CREATE TRIGGER mimir_cancelled_execution_wakeup
AFTER INSERT ON mimir_operation_cancellations
FOR EACH ROW EXECUTE FUNCTION mimir_operation_cancelled();
