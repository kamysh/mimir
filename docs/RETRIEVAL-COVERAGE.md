# Knowing what a belief search actually did

`query_relevant` returns an object with `beliefs` and `retrieval`. With `include_evidence=true`, each belief still includes its supporting passages. `query_learning_context` keeps its existing beliefs, procedures and assessments and adds the same `retrieval` report for its belief search.

The report contains the submitted `context`, semantic-search status and reason, actual matching method, a readable message, the consequence for result coverage and a next step. Missing semantic search does not mean a literal context is invalid or meaningless. Error codes, identifiers and configuration fragments can be useful keyword queries.

For example, when embeddings are intentionally unconfigured:

```json
{
  "beliefs": [],
  "retrieval": {
    "context": "E0412_literal_identifier",
    "semantic_search": {
      "status": "unavailable",
      "reason": "not_configured",
      "cause": null
    },
    "matching_performed": "keyword",
    "message": "Semantic search was not performed because no embedding backend is configured. These results use keyword matching; semantic similarity was not evaluated.",
    "coverage": "Results cover literal matches and any graph connections derived from them. Beliefs related only by semantic similarity may be missing.",
    "next_step": "Use these results for literal matching. If semantic matching is needed, ask the user to configure an embedding backend and repeat this query."
  }
}
```

This example assumes searchable beliefs exist but none matched. If the requested scope has no eligible beliefs at all, the report instead says `not_performed`, reason `no_eligible_beliefs`, with matching `none`. The backend is not called in that case.

A configured backend failure uses reason `embedding_failed` and retains its complete actual cause. A response without one finite, nonempty, nonzero query vector uses reason `unusable_query_vector`. Keyword results remain available with an explicit warning about missing semantic coverage. A completed semantic lookup says `available`, reason `evaluated`, and matching `keyword_and_semantic`.

This nonzero requirement comes from cosine similarity's domain, not a result quota or accuracy threshold. For example, the maintained PostgreSQL fixture returns `NaN` for the cosine distance from `[0,0,0]` to `[1,0,0]`; it returns `0` from `[1,0,0]` to itself. An all-zero query cannot establish semantic similarity, so its report explains that cause and keeps the keyword results.

This availability report covers embedding preparation. A failure while reading stored vectors or other database rows still follows the existing database diagnostic and recovery path. It is not relabelled as semantic success or an empty search result.

The CLI prints the context, message, coverage and next step before the beliefs. Prompt and pre-tool hooks carry the same notice; the pre-tool hook retains one valid JSON output object. The judge reads beliefs from the named array and preserves the report for the calling model. Consumers of older array-only `query_relevant` responses must switch to `result.beliefs` and inspect `result.retrieval`.

Mimir does not guess whether a context has semantic meaning, automatically choose another model, shorten input or change the user's configuration. These reports describe observed work and coverage; they do not create an experience, usage count or other business write.
