## mimir — persistent reasoning across sessions

Mimir preserves decisions, rejected approaches, constraints and lessons from
failures. Before choosing an approach, investigating an unfamiliar subsystem or
diagnosing a surprising error, a focused query can recover reasoning that would
otherwise have to be reconstructed. At startup, resume or after compaction,
identify which gaps prior knowledge could fill.

Use `query_relevant` with a focused question and the project when known. Compare
returned beliefs with each other and current evidence; explain consequential
changes to the approach. Probability is evidence to evaluate, not an instruction
to obey. Project scoping belongs on the query; no marker-file declaration is needed.

Preserve durable, non-obvious findings that would help a future session. Choose
`fact` or `experiential` explicitly for durable beliefs. Use `working` only for
intentional temporary memory and track its resolution; it is excluded from
cross-session retrieval. The standard setup has no automatic consolidation gate.
Read the `mimir` skill for tool choice, evidence and writeback details.

For approach choices, `query_learning_context` includes procedures and observed
outcomes. Capture meaningful action/outcome evidence with `record_experience`
when authorized, preserving incident IDs on retries and corrections. The optional
background judge reviews these observations. When retrieved context guides a
later action, record its observed result with the used belief or pattern ID;
retrieval alone is not successful use. Direct `insert_belief` now requires an
independent user instruction or document reference; incident-derived claims go
through experience-owned review candidates.

The lifecycle reminder supplies guidance rather than automatic queries, mandatory
calls, ratings or per-turn writeback. When Muninn is also installed, use it to
locate code and repository notes, and Mimir for lessons affecting the approach.
