{-# OPTIONS --safe #-}
-- Bind the nine embedded SQL bodies to their application DDL contracts.
-- SQL whitespace is ignored only at the script boundary, as by the loader;
-- statements, constraints and constants within a body remain exact.
module Mimir.MigrationScriptBinding where

open import Data.List using (List; []; _∷_)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Mimir.Text using (Text; trim)
import Mimir.MigrationSchema as Schema
import Mimir.MigrationLedger as Ledger

source : Schema.Migration → Text
source Schema.initial = toList "SELECT ag_catalog.create_graph(current_database()::text)\nWHERE NOT EXISTS (\n    SELECT 1 FROM ag_catalog.ag_graph WHERE name = current_database()::text\n);\n\n-- Vertex labels\nDO $$ BEGIN PERFORM ag_catalog.create_vlabel(current_database()::text, 'Belief');        EXCEPTION WHEN others THEN NULL; END $$;\nDO $$ BEGIN PERFORM ag_catalog.create_vlabel(current_database()::text, 'Pattern');       EXCEPTION WHEN others THEN NULL; END $$;\nDO $$ BEGIN PERFORM ag_catalog.create_vlabel(current_database()::text, 'DocumentChunk'); EXCEPTION WHEN others THEN NULL; END $$;\n\n-- Edge labels\nDO $$ BEGIN PERFORM ag_catalog.create_elabel(current_database()::text, 'SUPPORTS');    EXCEPTION WHEN others THEN NULL; END $$;\nDO $$ BEGIN PERFORM ag_catalog.create_elabel(current_database()::text, 'DEFEATS');     EXCEPTION WHEN others THEN NULL; END $$;\nDO $$ BEGIN PERFORM ag_catalog.create_elabel(current_database()::text, 'CAUSES');      EXCEPTION WHEN others THEN NULL; END $$;\nDO $$ BEGIN PERFORM ag_catalog.create_elabel(current_database()::text, 'CONTRADICTS'); EXCEPTION WHEN others THEN NULL; END $$;\nDO $$ BEGIN PERFORM ag_catalog.create_elabel(current_database()::text, 'CONTAINS');    EXCEPTION WHEN others THEN NULL; END $$;\n\n-- pgvector embeddings table (agtype cannot store the vector type)\nCREATE TABLE IF NOT EXISTS public.chunk_embeddings (\n    chunk_id  UUID PRIMARY KEY,\n    embedding vector\n);\n"
source Schema.searchPath = toList "DO $$ BEGIN\n  EXECUTE format(\n    'ALTER DATABASE %I SET search_path = ag_catalog, \"$user\", public',\n    current_database()\n  );\nEND $$;\n"
source Schema.embeddingTable = toList "CREATE TABLE IF NOT EXISTS public.belief_embeddings (\n    belief_id UUID PRIMARY KEY,\n    embedding vector\n);\n"
source Schema.evidenceEdges = toList "DO $$ BEGIN PERFORM ag_catalog.create_elabel(current_database()::text, 'GROUNDS'); EXCEPTION WHEN others THEN NULL; END $$;\n"
source Schema.betaBeliefs = toList "DO $mig$\nBEGIN\n  EXECUTE format($cy$\n    SELECT * FROM ag_catalog.cypher(%L, $$\n      MATCH (n:Belief)\n      WHERE n.alpha0 IS NULL\n      SET n.alpha0 = n.probability * (2.0 + n.confidence * 198.0),\n          n.beta0  = (1.0 - n.probability) * (2.0 + n.confidence * 198.0),\n          n.alpha  = n.probability * (2.0 + n.confidence * 198.0),\n          n.beta   = (1.0 - n.probability) * (2.0 + n.confidence * 198.0)\n      RETURN count(n)\n    $$) AS (c ag_catalog.agtype)\n  $cy$, current_database());\nEND\n$mig$;\n"
source Schema.learning = toList "CREATE TABLE mimir_experiences (\n    id uuid PRIMARY KEY,\n    project text NOT NULL,\n    revision bigint NOT NULL CHECK (revision > 0),\n    review_revision bigint NOT NULL DEFAULT 0,\n    reviewed_revision bigint NOT NULL DEFAULT 0,\n    updated_at timestamptz NOT NULL DEFAULT now()\n);\nCREATE TABLE mimir_experience_versions (\n    experience_id uuid NOT NULL REFERENCES mimir_experiences(id) ON DELETE CASCADE,\n    revision bigint NOT NULL,\n    payload jsonb NOT NULL,\n    created_at timestamptz NOT NULL DEFAULT now(),\n    PRIMARY KEY (experience_id, revision)\n);\nCREATE TABLE mimir_review_versions (\n    experience_id uuid NOT NULL REFERENCES mimir_experiences(id) ON DELETE CASCADE,\n    revision bigint NOT NULL,\n    experience_revision bigint NOT NULL,\n    payload jsonb NOT NULL,\n    created_at timestamptz NOT NULL DEFAULT now(),\n    PRIMARY KEY (experience_id, revision),\n    FOREIGN KEY (experience_id, experience_revision)\n      REFERENCES mimir_experience_versions(experience_id, revision)\n);\nCREATE INDEX mimir_pending_reviews ON mimir_experiences(updated_at, id)\n    WHERE reviewed_revision < revision;\n"
source Schema.candidates = toList "ALTER TABLE mimir_review_versions ADD COLUMN request jsonb;\nCREATE TABLE mimir_review_candidates (\n    experience_id uuid NOT NULL REFERENCES mimir_experiences(id) ON DELETE CASCADE,\n    candidate_key text NOT NULL CHECK (length(candidate_key) BETWEEN 1 AND 128),\n    kind text NOT NULL CHECK (kind IN ('belief', 'pattern')),\n    node_id uuid NOT NULL UNIQUE,\n    declaration jsonb NOT NULL,\n    retired boolean NOT NULL DEFAULT false,\n    PRIMARY KEY (experience_id, candidate_key)\n);\nCREATE INDEX mimir_review_candidates_node ON mimir_review_candidates(node_id);\n"
source Schema.assessment = toList "CREATE TABLE mimir_assessment_contributions (\n    experience_id uuid NOT NULL,\n    review_revision bigint NOT NULL,\n    belief_id uuid NOT NULL,\n    scope text NOT NULL,\n    rubric text NOT NULL,\n    positive double precision NOT NULL CHECK (positive BETWEEN 0 AND 1),\n    negative double precision NOT NULL CHECK (negative BETWEEN 0 AND 1),\n    benefit double precision NOT NULL CHECK (benefit BETWEEN -1 AND 1),\n    benefit_weight double precision NOT NULL CHECK (benefit_weight BETWEEN 0 AND 1),\n    payload jsonb NOT NULL,\n    PRIMARY KEY (experience_id,review_revision,belief_id,scope,rubric),\n    FOREIGN KEY (experience_id,review_revision)\n      REFERENCES mimir_review_versions(experience_id,revision) ON DELETE CASCADE,\n    CHECK (positive + negative <= 1.000000000000001),\n    CHECK (abs(benefit) <= benefit_weight)\n);\nCREATE INDEX mimir_assessment_lookup ON mimir_assessment_contributions(belief_id,scope,rubric);\n"
source Schema.owners = toList "CREATE TABLE mimir_learning_item_owners (\n    item_id uuid PRIMARY KEY,\n    experience_id uuid NOT NULL REFERENCES mimir_experiences(id) ON DELETE CASCADE,\n    source_ref text NOT NULL,\n    actor text NOT NULL\n);\n"

data Statement : Set where
  application : Schema.DDL → Statement
  transactionSearchPath : List Text → Statement
  dropLegacyLedger : Statement

data Meaning (original : Text) : List Statement → Set where
  embedded : ∀ migration → trim original ≡ trim (source migration) →
    Meaning original (Data.List.map application (Schema.body migration))
  localPath : trim original ≡ toList "SET LOCAL search_path TO public,ag_catalog" →
    Meaning original (transactionSearchPath (toList "public" ∷ toList "ag_catalog" ∷ []) ∷ [])
  legacyDrop : trim original ≡ toList "DROP TABLE IF EXISTS _sqlx_migrations" →
    Meaning original (dropLegacyLedger ∷ [])

record Embedded (migration : Schema.Migration) (loaded : Ledger.Migration) : Set where
  field named : Ledger.Migration.name loaded ≡ toList (Schema.migrationName migration)
        body : trim (Ledger.Metadata.script (Ledger.Migration.payload loaded)) ≡ trim (source migration)

-- This receipt connects executeOriginalSQL/executeScript to the exact loaded
-- body, while MigrationRuntime retains transaction/lock/checksum/ledger order.
meaning : ∀ migration loaded → Embedded migration loaded →
  Meaning (Ledger.Metadata.script (Ledger.Migration.payload loaded))
    (Data.List.map application (Schema.body migration))
meaning migration loaded loadedSource = embedded migration (Embedded.body loadedSource)
