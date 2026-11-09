-- #!migration
-- name: "review-queue-notifications",
-- description: "Signal committed pending-experience changes without exposing source content. The durable queue remains authoritative.",
-- requires: "postgres-item-allocation";

CREATE FUNCTION public.mimir_notify_review_queue() RETURNS trigger
LANGUAGE plpgsql AS $$
BEGIN
    IF NEW.reviewed_revision < NEW.revision THEN
        IF TG_OP = 'INSERT' THEN
            PERFORM pg_notify('mimir_review_queue_changed', '');
        ELSIF OLD.revision IS DISTINCT FROM NEW.revision
           OR OLD.project IS DISTINCT FROM NEW.project
           OR OLD.reviewed_revision >= OLD.revision THEN
            PERFORM pg_notify('mimir_review_queue_changed', '');
        END IF;
    END IF;
    RETURN NEW;
END;
$$;

-- PostgreSQL publishes transactional notifications at commit and discards them
-- on rollback. Identical notifications may be coalesced within a transaction:
-- a listener must scan the queue rather than count signals or treat one as a
-- saved review receipt. Updates that only acknowledge a review do not wake it.
CREATE TRIGGER mimir_review_queue_changed
AFTER INSERT OR UPDATE OF revision, reviewed_revision, project
ON public.mimir_experiences
FOR EACH ROW EXECUTE FUNCTION public.mimir_notify_review_queue();
