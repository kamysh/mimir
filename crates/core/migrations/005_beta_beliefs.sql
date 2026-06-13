-- #!migration
-- name: "beta-beliefs",
-- description: "Phase 3 (spec/Mimir/Beta.agda): make the durable belief state the Beta pair. Each Belief vertex gains a fixed prior (alpha0, beta0) and a posterior (alpha, beta) initialised to the prior, derived from its current (probability, confidence) via the prior mapping (graph.rs::prior_from, KAPPA_MIN=2, KAPPA_MAX=200): kappa = 2 + confidence * 198 alpha0 = probability * kappa,        beta0 = (1 - probability) * kappa alpha  = alpha0,                     beta  = beta0 The mapping preserves the mean EXACTLY: alpha0/(alpha0+beta0) = probability, so a backfilled belief loads with mean == its old probability — the durable state required by Mimir.Beta.store-load-round-trip (probability/confidence are now DERIVED on load, not independently stored scalars). Idempotent: only vertices missing alpha0 are touched, so this is a no-op on rows already backfilled by an earlier run. AGE's cypher() needs the graph name as a literal; build it with EXECUTE format(%L, current_database()) so it runs on the live graph and on any throwaway test DB (graph name = database name, per migration 001).",
-- requires: "evidence-edges";
DO $mig$
BEGIN
  EXECUTE format($cy$
    SELECT * FROM ag_catalog.cypher(%L, $$
      MATCH (n:Belief)
      WHERE n.alpha0 IS NULL
      SET n.alpha0 = n.probability * (2.0 + n.confidence * 198.0),
          n.beta0  = (1.0 - n.probability) * (2.0 + n.confidence * 198.0),
          n.alpha  = n.probability * (2.0 + n.confidence * 198.0),
          n.beta   = (1.0 - n.probability) * (2.0 + n.confidence * 198.0)
      RETURN count(n)
    $$) AS (c ag_catalog.agtype)
  $cy$, current_database());
END
$mig$;
