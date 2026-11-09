-- #!migration
-- name: "decay-accounting",
-- description: "Record the time already represented by current belief counts. Initialize missing baselines at one PostgreSQL time without changing any count, prior, probability or existing baseline.",
-- requires: "operation-cancellations";
DO $migration$
DECLARE
  baseline text := to_char(clock_timestamp() AT TIME ZONE 'UTC', 'YYYY-MM-DD"T"HH24:MI:SS.US"Z"');
BEGIN
  EXECUTE format($query$
    SELECT * FROM ag_catalog.cypher(%L, $cypher$
      MATCH (n:Belief)
      WHERE n.decay_accounted_at IS NULL
      SET n.decay_accounted_at = %L
      RETURN count(n)
    $cypher$) AS (count ag_catalog.agtype)
  $query$, current_database(), baseline);
END
$migration$;
