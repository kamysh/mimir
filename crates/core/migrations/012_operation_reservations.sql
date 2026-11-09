-- #!migration
-- name: "operation-reservations",
-- description: "Reserve PostgreSQL-issued operation tokens without changing business records or imposing expiry.",
-- requires: "review-queue-notifications";

CREATE TABLE mimir_operation_reservations (
    operation_token uuid PRIMARY KEY DEFAULT gen_random_uuid(),
    reserved_at timestamptz NOT NULL DEFAULT now()
);
