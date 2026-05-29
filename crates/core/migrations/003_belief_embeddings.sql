-- pgvector embeddings for beliefs (parallel to chunk_embeddings for documents).
--
-- Beliefs are stored as AGE graph nodes and agtype cannot hold the `vector`
-- type, so belief embeddings live in this public side table keyed by belief id.
-- query_relevant does cosine nearest-neighbour over this table
-- (ORDER BY embedding <=> $query_vec) as the vector half of hybrid retrieval.
-- Rows are written on insert_belief (when an embedding backend is configured)
-- and backfilled by `mimir reembed`; they are deleted alongside their belief in
-- delete_belief / delete_project.
CREATE TABLE IF NOT EXISTS public.belief_embeddings (
    belief_id UUID PRIMARY KEY,
    embedding vector
);
