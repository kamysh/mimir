---
name: mimir
description: Use whenever mcp__mimir tools are available — after every non-trivial turn, ask whether anything you learned, derived, or got corrected on belongs in the belief graph. Bias hard toward inserting. The graph only grows if you act on the bias.
---

# Mimir

You have a persistent belief graph. The `UserPromptSubmit` hook runs `query_relevant` before each user message and surfaces matching beliefs. **You also need to write to the graph.** The failure mode you keep falling into is treating `query_relevant` as a checkbox and never calling `insert_belief` / `insert_pattern`. Stop doing that.

## The mandate

After every non-trivial exchange, *before composing your final reply*, ask one question:

> Did I just learn, surface, or get corrected on something that — if true at the start of this session — would have changed what I did, **and** would plausibly apply in a future session?

If yes, insert it. If you need to think longer than five seconds about whether it qualifies, insert it. The cost of a redundant insert is small; the cost of losing a hard-won insight is large.

If during a turn you discover something insertable, **write the insert immediately**, then continue with the user-facing reply. Don't batch it for "later" — later is when the conversation is closed.

## Default: insert

Reverse the burden of proof. The decision is not *"should I insert this?"* but *"is there a clean reason **not** to?"*:

| Keep out | Insert |
|---|---|
| Already in CLAUDE.md / AGENTS.md / project docs | Generalises past this one codebase |
| Trivially derivable by reading code | Teaches something the docs don't capture |
| Purely ephemeral (today's PR #, today's path) — or tag `project=<name>` and `delete_project` on completion | The user corrected you (calibrate confidence to your residual uncertainty) |
| Restatement of language docs / stdlib behavior | Required reading two failed attempts to discover |

## Mechanics — the actual tool calls

Three primary mutators (full schemas in `mcp__mimir__*`; if you forget the parameter list mid-task, run `ToolSearch` with `select:mcp__mimir__insert_belief,mcp__mimir__insert_pattern` to load them inline):

- `insert_belief(content, probability, confidence, project?)` — a factual claim with epistemic state. `content` is a sentence or short paragraph; `probability` and `confidence` are 0.0–1.0 floats. Pass `project="<name>"` for project-scoped beliefs that get bulk-deleted with `delete_project`.
- `insert_pattern(situation, approach, success_rate)` — a "when X, do Y" rule. `situation` describes the trigger; `approach` the action. `success_rate` is your estimate of how often the approach is correct (0.0–1.0). Note the third field is `success_rate`, not `confidence`.
- `record_support(observation_id, belief_id, weight)` / `record_defeat(observation_id, belief_id, weight)` — link a freshly-inserted observation to an existing belief. `defeat` cascades to dependents; `support` reinforces.

Other useful tools: `get_belief`, `list_beliefs`, `update_confidence`, `delete_belief`, `delete_pattern`, `get_contradictions`, `propagate_from`.

## Triggers — situations where you should almost always insert

1. **Debugging took more than two failed attempts.** That's the shape of a tomorrow-Claude trap.
2. **You picked a library / dep / approach and discovered it's worse than it looked.** Insert the anti-pattern + the test that would have surfaced it earlier.
3. **You found infrastructure that violates a "should just work" assumption.** Examples: package registries rejecting default User-Agents, CI environments masking local-only effects, version coupling between separately-managed pieces, build sandboxes that block network and require pre-fetched mirrors, fixed-output derivations that look identical but aren't cache-hit-able.
4. **You got corrected by the user.** Especially if the correction reveals a *class* of mistake (not just a one-off).
5. **You proposed N approaches and the user picked the unobvious one.** The reasoning behind their choice is the belief.
6. **You ran a postmortem (anything starting with "why did this fail?").** Each non-trivial conclusion is a candidate.
7. **A sequence of steps works while the obvious sequence doesn't.** Insert as `insert_pattern` (situation + approach).
8. **A user preference is stable across multiple turns** — e.g. a writing style, a tool preference, an install-path convention. Even if also in auto-memory, mirror it as a belief for cross-project carryover.

## During work — observe and link

- New observation confirms an existing belief → `record_support(observation_id, belief_id, weight)`
- New observation contradicts → `record_defeat(observation_id, belief_id, weight)` (cascades to dependents)
- Two beliefs disagree (`get_contradictions`) → reconcile by `update_confidence` or `record_defeat`

## Calibration

Never `probability=1.0, confidence=1.0` unless it's a hard constraint with catastrophic consequence — flat saturation is information-free. When unsure of the right row, pick the lower one and revisit when corroborated.

| Type | probability | confidence |
|---|---|---|
| Hard constraint, catastrophic if violated | 1.0 | 1.0 |
| Strong widely-applicable heuristic | 0.90–0.98 | 0.85–0.95 |
| Useful but context-dependent rule | 0.60–0.85 | 0.70–0.90 |
| Project-specific hint | 0.20–0.40 | 0.60–0.80 |

## Concrete examples — shapes that earn an insert

Real cases (anonymised) from past sessions where the insert *should* have happened and didn't:

- **Belief**: "crates.io 403s `curl/X.Y.Z` UA on `/api/v1/crates/<n>/<v>/download`; Nix builds that hit it need a `fetchurl` overlay injecting a contact-bearing UA. Warm local `/nix/store` masks the failure — only fresh CI runners or `nix-collect-garbage`'d stores exhibit it."  *Trigger: spent 30+ minutes debugging a CI failure that didn't reproduce locally.*  *probability 0.90, confidence 0.85*

- **Belief**: "When pinning a vendored ML runtime archive (Pyke onnxruntime) in flake.nix, also pin the consuming `*-sys` crate to exactly the matching ABI version via a direct workspace dep. Loose `=2.0.0-rc` lets `cargo update` silently bump → runtime panic `Failed to initialize ORT API` because the binary calls a newer `OrtGetApi(N)` against an older `libonnxruntime.a`."  *Trigger: shipped two broken releases before noticing.*  *probability 0.95, confidence 0.90*

- **Belief**: "`fastembed` silently truncates input to the model's max-token context. Swapping to a stricter wrapper (e.g. tessera v0.1.0) makes previously-truncated chunks surface as opaque batch errors. Fix in the chunker (cap chunk size to fit the model context), not the embedder wrapper."  *probability 0.85, confidence 0.80*

- **Pattern**: situation *"evaluating a library swap"*, approach *"spike with realistic inputs from the actual target project, not minimal `hello world` strings. v0.1.x crates often pass smoke tests and fail on real data."*  *success_rate 0.85*

- **Pattern**: situation *"CLI emits per-item warnings while running a `\r`-redrawing progress bar"*, approach *"collect warnings into a structured `Vec` returned from the operation; CLI prints after the progress completes. Do not rely on `tracing::warn!` reaching the user's eyeballs."*  *success_rate 0.95*

If you write 2–3 inserts at the end of a multi-step task, you are *not* over-doing it — that is the cadence the skill asks for.

## Honest self-check before closing a conversation

When you reach a natural stopping point and feel the urge to summarise and move on, stop and ask:

1. Did I write *anything* to mimir in this conversation? If no, am I genuinely certain nothing was worth inserting?
2. Did the user correct me at any point in ways I haven't recorded?
3. Did I solve a problem whose solution was non-obvious enough that a future Claude would re-derive it from scratch?
4. Was any infrastructure / tooling quirk surfaced that surprised me?

If any answer nags you, **insert before closing**. That nag is the signal.
