-- Idempotent initial schema for mimir.
--
-- Extensions (age, vector, uuid-ossp, pgcrypto) are installed by
-- create-db-user.sh with superuser privileges and are not repeated here.
--
-- The AGE graph name equals the PostgreSQL database name.

-- Create the AGE graph if it doesn't already exist.
SELECT ag_catalog.create_graph(current_database()::text)
WHERE NOT EXISTS (
    SELECT 1 FROM ag_catalog.ag_graph WHERE name = current_database()::text
);

-- Vertex labels
DO $$ BEGIN PERFORM ag_catalog.create_vlabel(current_database()::text, 'Belief');        EXCEPTION WHEN others THEN NULL; END $$;
DO $$ BEGIN PERFORM ag_catalog.create_vlabel(current_database()::text, 'Pattern');       EXCEPTION WHEN others THEN NULL; END $$;
DO $$ BEGIN PERFORM ag_catalog.create_vlabel(current_database()::text, 'DocumentChunk'); EXCEPTION WHEN others THEN NULL; END $$;

-- Edge labels
DO $$ BEGIN PERFORM ag_catalog.create_elabel(current_database()::text, 'SUPPORTS');    EXCEPTION WHEN others THEN NULL; END $$;
DO $$ BEGIN PERFORM ag_catalog.create_elabel(current_database()::text, 'DEFEATS');     EXCEPTION WHEN others THEN NULL; END $$;
DO $$ BEGIN PERFORM ag_catalog.create_elabel(current_database()::text, 'CAUSES');      EXCEPTION WHEN others THEN NULL; END $$;
DO $$ BEGIN PERFORM ag_catalog.create_elabel(current_database()::text, 'CONTRADICTS'); EXCEPTION WHEN others THEN NULL; END $$;
DO $$ BEGIN PERFORM ag_catalog.create_elabel(current_database()::text, 'CONTAINS');    EXCEPTION WHEN others THEN NULL; END $$;

-- pgvector embeddings table (agtype cannot store the vector type)
CREATE TABLE IF NOT EXISTS public.chunk_embeddings (
    chunk_id  UUID PRIMARY KEY,
    embedding vector
);
