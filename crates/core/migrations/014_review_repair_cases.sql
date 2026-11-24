-- #!migration
-- name: "review-repair-cases",
-- description: "Keep the actionable remedy for an unresolved review until its source is reviewed or replaced.",
-- requires: "review-work-events";
CREATE TABLE mimir_review_repair_cases (
    experience_id uuid NOT NULL,
    source_revision bigint NOT NULL,
    remedy jsonb NOT NULL,
    PRIMARY KEY (experience_id, source_revision),
    FOREIGN KEY (experience_id, source_revision)
        REFERENCES mimir_experience_versions(experience_id, revision) ON DELETE CASCADE
);
CREATE TRIGGER mimir_review_repair_work_changed
AFTER INSERT OR UPDATE OR DELETE ON mimir_review_repair_cases
FOR EACH ROW EXECUTE FUNCTION mimir_signal_review_work();
