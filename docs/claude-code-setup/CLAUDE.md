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
  `insert_belief`. One claim per belief, scoped to the project.
- `probability` = how true it is; `confidence` = how sure you are. A verified fact is
  ~(0.95, 0.9); a working hypothesis ~(0.7, 0.5).
- Link beliefs only when the relation is real: `record_support`, `record_defeat`,
  `record_cause`, `record_contradiction`. Do not invent edges.
- Do **not** write: ephemeral state, secrets, anything obvious from the code or docs,
  or personal/unrelated notes (code locations belong in muninn, not mimir).

### Cost discipline

- Do not query or write on trivial tasks. A query that will not change what you do is
  wasted context; mimir earns its place only when a belief saves real exploration.
