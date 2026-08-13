# Claude Code instructions for mimir (`CLAUDE.md`)

This is the **standing policy** Claude Code should carry in every session that works
in a mimir-backed repo. It is different in kind from the two other install-now
artifacts:

- the **skill** (`10`) is the on-demand manual — loaded when Claude decides mimir is
  relevant;
- the **hooks** (`20`) are the plumbing — they push relevant beliefs into context
  automatically, with no action from Claude;
- this **`CLAUDE.md`** is the always-loaded behavioral contract — the few rules that
  must hold every turn.

Save the block below as `CLAUDE.md` in the repo root (or merge it into an existing
one). Keep it short on purpose: `CLAUDE.md` is loaded on every turn, so length here
is a tax on attention and context. Everything detailed lives in the skill.

The main body assumes only what mimir does **today**. The trailing block applies once
Phase 4 evidence edges (`60`) are in.

---

```markdown
## mimir — persistent belief graph

This repo uses mimir to carry what past sessions learned across context compaction
and new sessions. Relevant beliefs are injected automatically by the session hooks —
you do not need to query mimir at startup.

### Reading beliefs
- Treat an injected belief with **p ≥ 0.8 as the default action**: follow it unless
  you have concrete evidence it is wrong *in this case*. If you override one, say why
  in a single line.
- A belief is a **prior, not ground truth**. Beliefs with p < 0.8 are hints — weigh
  them, do not obey them.
- When a specific question comes up mid-task ("did we decide X?", "does Y work in this
  repo?"), pull with `query_relevant` before re-deriving it from scratch.

### Writing beliefs
- After you find something **durable, non-obvious, and project-specific** — a gotcha,
  a decision and its rationale, a constraint that cost you exploration — record it with
  `insert_belief` as `memory_type: fact` or `experiential` (see below for the
  distinction). One claim per belief, scoped to the project.
- `probability` = how true it is; `confidence` = how sure you are. A verified fact is
  ~(0.95, 0.9); a working hypothesis ~(0.7, 0.5).
- Link beliefs only when the relation is real: `record_support`, `record_defeat`,
  `record_contradiction`. Do not invent edges.
- When a new belief supersedes an older one, call `record_defeat` on the old belief
  immediately — in the same turn, not later. An un-defeated superseded belief is
  indistinguishable from a live one in `query_relevant` results.
- Do **not** write: secrets or credentials, anything already obvious from the code or
  docs, or personal/unrelated notes (those belong in muninn, not mimir). Ephemeral
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
- **Consolidate at natural session-end points**: review the `working` beliefs YOUR
  session wrote — track their IDs yourself as you create them, since
  `list_beliefs(memory_type="working")` has no session-identity concept and cannot
  distinguish your in-flight beliefs from a concurrent session's on a shared DB (that
  filter exists mainly for orphan cleanup of leftovers from an interrupted prior
  session). For each: promote (rewrite as `fact`/`experiential`, delete the working
  original) or discard (delete without promoting). Also available as an explicit
  on-demand action.

### Cost discipline
- Do not query or write `fact`/`experiential` beliefs on trivial tasks — a query that
  won't change what you do is wasted context; mimir earns its place only when a belief
  saves real exploration. This does not apply to `working` beliefs, which are meant to
  be cheap.
```

---

### Trailing block — add once Phase 4 evidence edges are enabled

```markdown
### Documents as evidence
- If a belief comes from a document, **ground it**: after loading the doc, call
  `add_evidence(chunk_id, belief_id)`. Query with `--evidence` so retrieval returns
  the source passage alongside the belief.
- Before overriding a **grounded** belief, read its passage first. When you act on a
  grounded belief, cite the passage.
```

## Note on overlap with the hooks

The hooks already retrieve at session start and on each prompt, so this file does not
tell Claude to query at startup — that would duplicate the plumbing and waste turns.
`CLAUDE.md` covers only what the hooks cannot: the override discipline, when to *write*,
and (with Phase 4) when to ground and cite. If you later tune the hooks to also do
mid-task `PreToolUse` retrieval, drop the "pull with `query_relevant` mid-task" line to
avoid double-querying.
