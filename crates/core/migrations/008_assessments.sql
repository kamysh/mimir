-- #!migration
-- name: "learning-assessments",
-- description: "Immutable typed assessment contributions owned by review versions; existing graph probabilities are unchanged.",
-- requires: "review-candidates";
CREATE TABLE mimir_assessment_contributions (
    experience_id uuid NOT NULL,
    review_revision bigint NOT NULL,
    belief_id uuid NOT NULL,
    scope text NOT NULL,
    rubric text NOT NULL,
    positive double precision NOT NULL CHECK (positive BETWEEN 0 AND 1),
    negative double precision NOT NULL CHECK (negative BETWEEN 0 AND 1),
    benefit double precision NOT NULL CHECK (benefit BETWEEN -1 AND 1),
    benefit_weight double precision NOT NULL CHECK (benefit_weight BETWEEN 0 AND 1),
    payload jsonb NOT NULL,
    PRIMARY KEY (experience_id,review_revision,belief_id,scope,rubric),
    FOREIGN KEY (experience_id,review_revision)
      REFERENCES mimir_review_versions(experience_id,revision) ON DELETE CASCADE,
    CHECK (positive + negative <= 1.000000000000001),
    CHECK (abs(benefit) <= benefit_weight)
);
CREATE INDEX mimir_assessment_lookup ON mimir_assessment_contributions(belief_id,scope,rubric);
