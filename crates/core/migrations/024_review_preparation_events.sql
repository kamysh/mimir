-- #!migration
-- name: "review-preparation-events",
-- description: "Stop owned review preparation when its source, review or candidate state changes, separately from the pending review queue.",
-- requires: "belief-sources";

-- Hints for owned preparation, not new-work scheduling. A feedback-only
-- acknowledgement must revoke stale preparation without making a queue loop.
CREATE FUNCTION public.mimir_notify_review_state_changed() RETURNS trigger
LANGUAGE plpgsql AS $$
BEGIN
    PERFORM pg_notify('mimir_review_state_changed', '');
    RETURN NULL;
END
$$;

CREATE TRIGGER mimir_review_source_state_changed
AFTER UPDATE OF revision, review_revision, project OR DELETE ON public.mimir_experiences
FOR EACH ROW EXECUTE FUNCTION public.mimir_notify_review_state_changed();

CREATE TRIGGER mimir_review_candidate_state_changed
AFTER INSERT OR UPDATE OR DELETE ON public.mimir_review_candidates
FOR EACH ROW EXECUTE FUNCTION public.mimir_notify_review_state_changed();
