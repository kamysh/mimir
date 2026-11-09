-- #!migration
-- name: "belief-sources",
-- description: "Retain explicitly cited indexed-document sources without assigning evidence weights or changing belief probability.",
-- requires: "decay-accounting";
CREATE TABLE public.mimir_belief_sources (
    belief_id UUID PRIMARY KEY REFERENCES public.belief_embeddings(belief_id) ON DELETE CASCADE,
    citations JSONB NOT NULL CHECK (jsonb_typeof(citations) = 'array')
);
