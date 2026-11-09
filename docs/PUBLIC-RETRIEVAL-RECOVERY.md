# Public retrieval recovery

`PublicRetrievalRecovery` accepts the six public search choices: context, result selection, project, memory-type preference, evidence inclusion and passage selection. Its input contains no embedding, selected beliefs, ranking or expected answer. The configured backend comes from the loaded core configuration.

The operation observes the database view, then requests an embedding for the complete context from that configured backend when eligible beliefs exist. An absent backend, a failed call or an unusable vector keeps its factual coverage explanation. A provider is not assumed to succeed or give the same result twice.

The expected response is calculated independently from the stored world and that observed external reply. `OrderedRetrieval` derives eligible beliefs, keyword and vector rankings, graph discovery, preference ranking and the caller's selection. A scoped search keeps the existing per-seed breadth-first discovery order: all initial seeds are already matched, each source's neighbors are ordered by identity, and newly discovered matches are appended. Unprocessed initial seeds remain pending until their own turn. This order matters because memory preference contributes ranking positions.

The traversal proof shows that every allowed reachable identity is found, that every discovered identity is reachable, and that no foreign identity is introduced. Every productive frontier round removes a stored entry from the not-yet-visited identities. The stored graph size therefore determines a sufficient number of expansions, including cycles and repeated entries. This is an exhaustion proof, not a selected work allowance. Every returned belief is also proved to be an eligible stored candidate.

When evidence is requested, grounding edges and indexed passages come from that same stored world. Only the caller's explicit passage selection applies. Enrichment preserves the selected beliefs and their order.

The exported operation certificate requires three proofs:

- A completed retry preserves the complete application world and returns the complete calculated response, including coverage and optional citations.
- A complete execution exists in the external-effect model. This is not a promise that an actual provider will respond or succeed.
- The receipt stored in the semantic result is exactly the observed execution transcript. It cannot name a different query or backend, or replace an embedding with a caller-supplied expected vector.

The receipt and stored snapshot are proof evidence, not additional public response fields. The success condition compares the complete semantic response; it is not a free predicate supplied by an operation.

The database boundary is the existing stable composite-read view. Individual SQL replies retain the meanings in `StorageReadBinding`. Connecting this certificate to mandatory dispatcher registration remains #74; checking all Rust statement boundaries against it remains separate work. Learning-context composition remains #135. This change does not claim those separate integration tasks are complete.
