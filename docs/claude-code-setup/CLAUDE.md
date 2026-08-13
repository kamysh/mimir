## mimir — persistent belief graph

This machine uses mimir to carry what past sessions learned across context compaction
and new sessions. Relevant beliefs are injected automatically by the session hooks —
you do not need to query mimir at startup.

### Reading beliefs — disposition required

When a belief arrives (injected by hook or retrieved mid-task):

- **p ≥ 0.8 → state your disposition before acting.** Either act consistently with it,
  or write one line explaining why you are overriding it. "Overriding: code changed in
  commit X" is valid. Silently proceeding as if the belief were absent is not.
- **p < 0.8 → hint.** Weigh it; do not obey it blindly.
- When a specific question arises mid-task ("did we decide X?", "does Y work here?"),
  call `query_relevant` before re-deriving from scratch.

### Writing beliefs

- After finding something **durable, non-obvious, and project-specific** — a gotcha, a
  decision and its rationale, a constraint that cost you exploration — record it with
  `insert_belief` as `memory_type: fact` or `experiential` (see below for the
  distinction). One claim per belief, scoped to the project.
- `probability` = how true it is; `confidence` = how sure you are. A verified fact is
  ~(0.95, 0.9); a working hypothesis ~(0.7, 0.5).
- Link beliefs only when the relation is real: `record_support`, `record_defeat`,
  `record_cause`, `record_contradiction`. Do not invent edges.
- When a new belief supersedes an older one, call `record_defeat` on the old belief
  immediately — in the same turn you write the new one, not later. An un-defeated
  superseded belief is indistinguishable from a live one in `query_relevant` results,
  so skipping this is how "mimir already had this, and I ignored it" happens.
- Do **not** write: secrets or credentials, anything obvious from the code or docs, or
  personal/unrelated notes (code locations belong in muninn, not mimir). Ephemeral
  in-task state is not banned outright — see Working memory below — but it is not
  written as `fact`/`experiential`.

### Memory types and consolidation (biological model: work now, consolidate later)

- `memory_type: fact` — declarative knowledge about code/environment. Decays over
  time absent reinforcement.
- `memory_type: experiential` — a hard-won working lesson (a gotcha, a corrected
  approach). Exempt from decay — its truth doesn't erode with elapsed time.
- `memory_type: working` — NOT a general log of in-session state (mimir is
  explicitly not a second brain for that — you already hold it in context). It is
  narrower: a **staging tier for a conclusion you're about to assert as
  `fact`/`experiential` but aren't yet confident will survive scrutiny**. Write it
  as `working` first; only promote to `fact`/`experiential` once it's held up under
  some reflection, rather than asserting it durable at first-draft confidence and
  correcting it later. They are excluded from cross-session `query_relevant`
  automatically.
- **Consolidate at natural session-end points** (task wrapping up, or asked to
  summarize/finish): review the `working` beliefs YOUR session wrote — track their
  IDs yourself as you create them; do not rely on `list_beliefs(memory_type="working")`
  for this, since that filter has no session-identity concept and on a shared DB with
  concurrent sessions cannot distinguish your in-flight beliefs from another session's
  (the `memory_type` filter exists mainly for orphan cleanup of leftovers from an
  interrupted prior session, where you'd review candidates before acting). For each
  Working belief: if it turned out durable and non-obvious, rewrite it as a proper
  `fact`/`experiential` belief via `insert_belief` and delete the working original; if
  it didn't pan out or was only useful in the moment, delete it without promoting.
  Don't leave consolidated-from originals lying around — the promoted belief (or
  nothing) is what should remain.
- This is also available as an explicit action if asked to "consolidate mimir" or
  similar, independent of any particular session ending.

### Cost discipline

- Do not query or write `fact`/`experiential` beliefs on trivial tasks — a query that
  won't change what you do is wasted context. This does not apply to `working`
  beliefs, which are meant to be cheap.
