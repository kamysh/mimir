-- #!migration
-- name: "operation-step-replies",
-- description: "Keep each step's original reply in the same transaction as its business change.",
-- requires: "operation-bindings";

CREATE TABLE mimir_operation_step_replies (
    operation_token uuid NOT NULL REFERENCES mimir_operation_bindings(operation_token),
    step text NOT NULL CHECK (step <> '' AND step = btrim(step)),
    reply jsonb NOT NULL,
    PRIMARY KEY (operation_token, step)
);

CREATE FUNCTION mimir_preserve_operation_step_reply() RETURNS trigger
LANGUAGE plpgsql AS $$
BEGIN
    RAISE EXCEPTION 'Step reply is immutable; read the original answer under this token and step'
        USING ERRCODE = '23514';
END;
$$;

CREATE TRIGGER mimir_operation_step_reply_immutable
BEFORE UPDATE OR DELETE ON mimir_operation_step_replies
FOR EACH ROW EXECUTE FUNCTION mimir_preserve_operation_step_reply();
