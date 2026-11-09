-- #!migration
-- name: "first-defeat-clock",
-- description: "Mark existing undated defeated targets as already past their waiting period. New defeats record their actual PostgreSQL time without replacing the first date.",
-- requires: "decay-accounting";
DO $migration$
BEGIN
  EXECUTE format($query$
    SELECT * FROM ag_catalog.cypher(%L, $cypher$
      MATCH (:Belief)-[:DEFEATS]->(target:Belief)
      WHERE target.first_defeated_at IS NULL
        AND target.legacy_defeat_expired IS NULL
      SET target.legacy_defeat_expired = true
      RETURN count(target)
    $cypher$) AS (count ag_catalog.agtype)
  $query$, current_database());
END
$migration$;
