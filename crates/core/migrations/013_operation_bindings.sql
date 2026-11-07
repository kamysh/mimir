-- #!migration
-- name: "operation-bindings",
-- description: "Keep each reserved token's original operation, arguments and settings immutable.",
-- requires: "operation-reservations";

CREATE TABLE mimir_operation_bindings (
    operation_token uuid PRIMARY KEY REFERENCES mimir_operation_reservations(operation_token),
    operation text NOT NULL CHECK (operation <> '' AND operation = btrim(operation)),
    arguments jsonb NOT NULL CHECK (jsonb_typeof(arguments) = 'object'),
    settings jsonb NOT NULL CHECK (jsonb_typeof(settings) = 'object'),
    bound_at timestamptz NOT NULL DEFAULT now()
);

CREATE FUNCTION mimir_preserve_operation_binding() RETURNS trigger
LANGUAGE plpgsql AS $$
BEGIN
    RAISE EXCEPTION 'Operation binding is immutable; read the existing binding and retry its original request'
        USING ERRCODE = '23514';
END;
$$;

CREATE TRIGGER mimir_operation_binding_immutable
BEFORE UPDATE OR DELETE ON mimir_operation_bindings
FOR EACH ROW EXECUTE FUNCTION mimir_preserve_operation_binding();
