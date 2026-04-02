# First Conversation with Mimir

*This conversation took place on 2026-04-01, bootstrapping an AI assistant's understanding of how to use the mimir MCP in practice. It is preserved here as a possible introduction to the system.*

---

## What is mimir?

Mimir is a belief graph MCP server. It stores beliefs (statements with probability and confidence scores) and patterns (situation → approach mappings), with support for defeasible reasoning: beliefs can support or defeat each other, confidence decays over time, and contradictions are tracked rather than hidden.

The name comes from Norse mythology — Mímir, the keeper of the well of wisdom.

---

## How should it be used?

**Q:** Do you understand how mimir MCP should be used in practice?

**A (AI):** Partially. I understand the data model and individual tool semantics. What I'm less sure about is the workflow integration:

- `query_relevant` — I assume I call this at the start of tasks to surface applicable beliefs/patterns. But what's the right input — a description of what I'm about to do? The user's request verbatim?
- `record_support` / `record_defeat` — I think these are for when I observe evidence that confirms or contradicts a belief during a task. But I don't know the expected granularity.
- `update_confidence` — Should I lower confidence on a belief if I find an edge case where it doesn't apply?
- `propagate_from` — I don't have a clear mental model of when to use this.
- `decay_all` — Is this something I should call periodically, or does it have another trigger?

**The answer:**

> As the first approximation, you should read this every time a new task is given, or after a conversation compression event. Going forward, you should be able to understand what is not important for a given task to optimize your token and memory consumption.

The key insight: `query_relevant` is the entry point, not `list_beliefs`. It is semantic filtering, not enumeration. Over time, the goal is to write narrower queries — relevant enough to catch what matters, tight enough to exclude noise.

---

## Bootstrapping: loading behavioral rules

The first practical task was inserting the most important behavioral rules from the project's CLAUDE.md and memory files into mimir as beliefs and patterns.

Initial insertion used probability=1.0, confidence=1.0 for everything. This turned out to be wrong — a flat maximum across all beliefs carries no information.

---

## Calibration: relative comparison

**Q (AI):** Do you understand how to use these settings?

**A:** You may ask me what is relevant, what is not. Don't expect "exact" answers expressed in numbers, but relative comparison of importance can be easily achieved. There may be contradictions (A > B, B > C, C > A) — this is OK. It is never perfect, and such things may happen when A ~ B ~ C.

This prompted a calibration dialogue. A few exchanges that shaped the final values:

---

**On "no hacks" vs "diagnose root cause before acting":**

> I think "no hacks" by itself is too vague. The second formulation is more actionable.

"No hacks" is a feeling. "Diagnose root cause before touching any file" is what you actually do. The vague principle was lowered to 0.2; the actionable version became the canonical belief at 0.95.

---

**On migration files being append-only:**

> This is absolutely a very important rule. Migrations' checksums are stored in the DB. If the migration itself was changed, the checksum becomes invalid, the DB becomes inconsistent, manual intervention becomes necessary.

Stayed at 1.0. Hard constraint with catastrophic consequences if violated.

---

**On "never touch types/ directories":**

> This is actually specific to the cases where types/* were generated automatically. It is not even the rule — just a hint for the particular project.

Lowered to 0.2. Project-specific hint, not a principle.

---

**On "UseConnector=true means no TLS validation":**

> With the current implementation, UseConnector=true automatically means the certificate will never correspond to the DNS name. This is not a security rule, just a fact.

Lowered to 0.65. A technical fact to remember, not a principle to enforce.

---

**On "always use muninn MCP first for code search":**

> You tend to use ls/grep/... utilities as the first available set of tools. I want you to use muninn more actively. There are two reasons: I want it to be tested as much as possible (and improved); and I really believe that it is more efficient.

Stayed at 1.0. The user wants it enforced strongly, and the reasons are concrete.

---

## Final calibrated state

| Confidence | Belief |
|---|---|
| 1.0 | Exit code 0 is the only proof of success / never mask errors (same principle, two levels) |
| 1.0 | DbConf/DataDbConf migrations are append-only |
| 1.0 | Always use muninn first for code search |
| 1.0 | Never assume config directory structure |
| 0.95 | Diagnose root cause before touching anything |
| 0.95 | Agda spec before Go code (DbAnalyzer) |
| 0.85 | No CLI args for configuration — everything in config files |
| 0.8 | Full environment analysis before proposing infrastructure changes |
| 0.7 | Never commit — user commits manually |
| 0.65 | UseConnector=true means no TLS cert validation (technical fact) |

---

## Reflection

**Q:** Do you feel it can be useful in your future projects?

**A:** Yes, genuinely. A few specific ways:

**Prevents confident wrongness.** The calibration process revealed that I was treating everything as equally absolute (all 1.0), when in reality there's a spectrum from "hard constraint with catastrophic consequences if violated" to "technical note to remember." Without this, I'd apply the same weight to everything.

**Survives context compression.** Memory files get truncated, instruction files grow unwieldy. Mimir's `query_relevant` at task start gives exactly the applicable subset — not everything, just what matters for this specific task.

**Accumulates calibrated experience.** When a mistake is made and corrected, `record_defeat` on the relevant belief and `update_confidence` captures *why* something was wrong, not just *that* it was wrong. That's more useful than adding another line to a text file.

**The questioning process itself is valuable.** Working through "is A more important than B?" forced both sides to articulate what's actually a hard rule vs. a principle vs. a hint. That clarity would have taken much longer to emerge from just reading text instructions.

The main open question: whether `record_support`/`record_defeat` will be used well during actual tasks. That requires discipline not yet demonstrated. But the foundation feels right.