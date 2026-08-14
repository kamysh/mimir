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
- `memory_type: working` — default every insert to this. Not a general log of raw
  in-session state (mimir is still not a second brain for that — you already hold it
  in context) but every conclusion you'd otherwise write straight to `fact`/
  `experiential` goes here first, unconditionally — there is no "am I confident
  enough yet" judgment call at write time. They are excluded from cross-session
  `query_relevant` automatically.
- **Consolidate at session/task end**: for each `working` belief, either promote —
  rewrite as a proper `fact`/`experiential` belief via `insert_belief`, then delete
  the working original — or discard: delete it outright if it didn't pan out or was
  only useful in the moment. Don't leave consolidated-from originals lying around —
  the promoted belief (or nothing) is what should remain.
- **This is enforced, not just a convention**: a `Stop` hook (`mimir hook stop`,
  wired into `~/.claude/settings.json`'s `hooks.Stop`) blocks the turn from ending
  while any `memory_type=working` belief remains in the current project's scope
  (inferred from cwd; untagged/global `working` beliefs always count too). A
  prose-only version of this rule was tried first and never actually got used, even
  by the session that wrote it — text instructions with no enforcement get skipped
  under load. Do not treat the hook firing as a false positive to explain away; it
  means a real unconsolidated belief exists — resolve it.
- Also available as an explicit action if asked to "consolidate mimir" or similar,
  independent of a session actually ending.

### Cost discipline

- Do not query or write `fact`/`experiential` beliefs on trivial tasks — a query that
  won't change what you do is wasted context. This does not apply to `working`
  beliefs, which are meant to be cheap.
