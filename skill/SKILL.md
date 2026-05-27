---
name: mimir
description: Use when mcp__mimir tools are available in the session — the belief graph only improves if Claude acts on retrieved results and writes observations back after each task
---

# Using Mimir

Mimir is a persistent belief graph. The `UserPromptSubmit` hook already fires `query_relevant` before every message. Your job is to **complete the loop**: act on what comes back, and write what you learn.

## The Loop

### Before the task — act on retrieved beliefs

The hook retrieves for you. Do not acknowledge results and move on — let them change what you do:

- **Matching belief** → apply it, or explicitly override it and note why
- **Matching pattern** → treat `approach` as your default strategy for this `situation`
- **No results** → proceed normally; stay alert for new insights

### During the task — observe and record

- Observation confirms a belief → `record_support(from_id=observation_id, to_id=belief_id, weight)`
- Observation contradicts a belief → `record_defeat(from_id=observation_id, to_id=belief_id, weight)` — this triggers a probability cascade through downstream beliefs automatically
- You learn something that would change how you handle a similar future task → `insert_belief`

**Threshold for inserting:** "Would this change my approach to a similar task in a future session?" If no, skip it.

### After the task — write what's worth keeping

- Novel reusable insight → `insert_belief`
- Approach that worked → `insert_pattern` (situation + approach + success_rate)
- Knowledge only valid for this project/task → tag with `project=<name>`; call `delete_project` when the work is complete

## Calibration

Never insert at flat probability=1.0, confidence=1.0 — that is information-free. Use relative comparison: if A matters more than B, then `A.probability > B.probability`.

| Type of belief | probability | confidence |
|----------------|-------------|------------|
| Hard constraint with known catastrophic consequence | 1.0 | 1.0 |
| Strong, widely-applicable heuristic | 0.90–0.98 | 0.85–0.95 |
| Useful but context-dependent rule | 0.60–0.85 | 0.70–0.90 |
| Project-specific hint | 0.20–0.40 | 0.60–0.80 |

Contradictions between high-probability beliefs (P(A) + P(B) > 1.0) are flagged by `get_contradictions` — use this to identify beliefs that need reconciliation.

## What NOT to insert

- Facts already in CLAUDE.md or derivable by reading the code
- Ephemeral task state (put in project scope if needed at all)
- Things only true right now that won't generalize
- Implementation details that belong in code comments or commit messages
