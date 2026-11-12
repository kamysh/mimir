-- #!migration
-- name: "review-work-events",
-- description: "Notify an idle watcher when reviewable work changes.",
-- requires: "postgres-item-allocation";
CREATE FUNCTION mimir_signal_review_work() RETURNS trigger LANGUAGE plpgsql AS $$
BEGIN
    PERFORM pg_notify('mimir_review_work', '');
    RETURN NULL;
END
$$;

CREATE TRIGGER mimir_review_work_changed
AFTER INSERT OR UPDATE OR DELETE ON mimir_experiences
FOR EACH STATEMENT EXECUTE FUNCTION mimir_signal_review_work();
