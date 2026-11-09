-- #!migration
-- name: "backfill-change-events",
-- description: "Wake owned backfill jobs after vector publication; existing product deletion and cancellation paths already notify in their own transactions. Listeners recheck the exact source and operation without a timer.",
-- requires: "decay-accounting";
CREATE TRIGGER mimir_backfill_vector_changed
AFTER INSERT OR UPDATE OR DELETE ON public.belief_embeddings
FOR EACH STATEMENT EXECUTE FUNCTION mimir_embedding_owner_changed();
