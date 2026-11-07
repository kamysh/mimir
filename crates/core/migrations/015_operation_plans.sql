-- #!migration
-- name: "operation-plans",
-- description: "Freeze registered steps and selected keys before business changes.",
-- requires: "operation-step-replies";

CREATE TABLE mimir_operation_plans (
    operation_token uuid PRIMARY KEY REFERENCES mimir_operation_bindings(operation_token),
    plan jsonb NOT NULL CHECK (jsonb_typeof(plan) = 'object')
);

CREATE FUNCTION mimir_preserve_operation_plan() RETURNS trigger
LANGUAGE plpgsql AS $$
BEGIN
    RAISE EXCEPTION 'Operation plan is immutable; read the original plan and saved answers'
        USING ERRCODE = '23514';
END;
$$;

CREATE TRIGGER mimir_operation_plan_immutable
BEFORE UPDATE OR DELETE ON mimir_operation_plans
FOR EACH ROW EXECUTE FUNCTION mimir_preserve_operation_plan();
