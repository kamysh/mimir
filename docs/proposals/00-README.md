# mimir × Claude Code — proposal set

Seven documents. Three are finished artifacts you install today; four are
implementation plans to hand to Claude Code, one phase at a time.

| File | Type | What it is |
|---|---|---|
| `10-mimir-SKILL.md` | **install now** | Rewritten skill, balanced read + write, with the "use a retrieved belief" discipline the current skill is missing. |
| `20-hooks-and-wiring.md` | **install now** | `settings.json` hook block + two helper scripts that put beliefs in front of Claude automatically, plus install/verify steps. |
| `70-claude-code-instructions.md` | **install now** | The project `CLAUDE.md` — the always-loaded standing policy for using mimir each session. Complements the skill (the on-demand manual) and the hooks (automatic injection). |
| `30-plan-do-operator.md` | plan → Claude Code | Phase 1. Give `CAUSES` real semantics via Pearl's do-operator as a *read-only* counterfactual query. Small, highest leverage. |
| `40-plan-logodds-propagation.md` | plan → Claude Code | Phase 2. Replace the order-dependent single-pass BFS with order-independent log-odds accumulation run to a fixpoint. |
| `50-plan-beta-beliefs.md` | plan → Claude Code | Phase 3 (optional). Collapse `probability` + `confidence` into one `Beta(α,β)`; updates become conjugate. Schema change. |
| `60-plan-evidence-edges.md` | plan → Claude Code | Phase 4. Make document chunks first-class evidence nodes (`GROUNDS` edges) so documents inform reasoning and carry provenance — with a proved non-interference guarantee. C-core ships independently; C-coupling composes with Phase 3. |

## The one idea behind all of it

Claude Code already reasons hypothetically *within* a session. mimir's job is
not to add a reasoning layer — it is to be the prior that survives what
in-session reasoning cannot: context compaction and session boundaries. Every
change here optimizes one quantity:

> **expected exploratory steps saved** = P(a relevant belief exists) × (steps it lets Claude skip) − (cost of the query)

The skill, hooks, and `CLAUDE.md` raise the first two factors (retrieval actually
happens, and the belief actually changes behavior). The code phases raise belief
*quality*: do-operator makes causal predictions trustworthy; log-odds makes
propagation well-defined instead of traversal-order-dependent; Beta makes
confidence a real quantity that updates rather than only decays; and evidence
edges let documents inform belief quality and supply provenance, so a fact with a
source is treated — and trusted — differently from a hunch.

## Recommended order

1. Install `10`, `20`, `70` — skill, hooks, `CLAUDE.md`. This is most of the
   practical win and needs no Rust. Run for a few sessions; see whether retrieval
   changes behavior.
2. Phase 1 do-operator (`30`) and Phase 4 C-core (`60`, first layer). Both are
   self-contained and carry no risk to existing inference — Phase 4's
   non-interference is proved. C-core also gives you provenance and the eval's
   `grounded` arm to measure whether documents actually help.
3. Phase 2 log-odds (`40`). Touches existing tests + the Agda proofs — do it when
   you want propagation you can trust on a dense graph.
4. Phase 3 Beta (`50`) only if Phases 1–2 prove the system earns its keep — and
   then Phase 4 C-coupling (the second layer of `60`), which depends on it.

## How to drive Claude Code through a plan

The plan files (`30`–`60`) are written to be pasted as the opening message of a
fresh Claude Code session *inside the mimir repo*, with the mimir + muninn tools
already wired. Each has an **Acceptance criteria** section — tell Claude Code to
treat those as a definition of done and to stop and report if any can't be met
rather than working around them. The plans deliberately reference exact file
paths, function names, and signatures as they exist in the repo today (verified
against the current `main`), so Claude Code should diff against reality first and
flag drift before editing. (`10`, `20`, and `70` are not plans — they install
directly.)
