# Completing cyclic posterior calculations

A posterior is complete only when every final alpha and beta equals the value
computed from that belief's fixed prior and all incoming evidence in the same
final state. Comparing probability changes with a chosen tolerance does not
establish this: different stored counts can show the same rounded probability.

Propagation has no pass allowance, elapsed-time deadline or approximate
stopping threshold. Acyclic graphs use dependency order. For a cycle, the
calculation checks every final equation after each sweep and remembers the
actual count states already observed.

Sometimes machine arithmetic repeats distinct states without satisfying those
equations. For example, two beliefs starting with probability 0.1 and confidence
0 can alternate between adjacent count values when one supports the other with
weight 1 and the other defeats the first with weight 0.7. Accepting either
iterate would silently introduce an accuracy policy.

When that happens, the caller receives `needs_input`, including the observed
values and instructions to open a user dialog. The agent must not choose an
iterate, change weights, invent a tolerance or automatically retry. The user
can cancel or discuss an explicit numerical policy. This change adds no
accuracy setting or default.

The calculation publishes no posterior while that decision is pending.
Transactions that stage a review, grounding or deletion roll back instead of
publishing their partial state. The current `record_defeat` path has an earlier
edge commit: its response explicitly identifies that committed edge and says
that no posterior was published. It must not claim that nothing changed.
Document loading and multi-item sweeping have their own earlier commits and
must not inherit an inner step's no-change claim.

## What the formal model checks

The numerical contract derives the targets, priors, feedback, grounding and
incoming edges from the initial stored world. Completed results must satisfy
every final equation, contain exactly the selected identities and preserve
every unrelated stored component. Intervention preserves the entire world.

A returned calculation report is untrusted. The model checks a candidate's
complete equations and input identities. A claimed repetition must replay the
observed sweeps through the uncapped transition system. Ending a finite report
in an intermediate state cannot count as completion. Float arithmetic and
display remain standard dependency boundaries; there is no proof of their
implementation or enumeration of their possible values.

These checks replace the former capped pure calculation used by propagation,
intervention, review publication, source correction, grounding and deletion.
The raw numerical observations are explicit dependencies, like observed
database identities; supplying them is not a proof that they are correct.

The shared recovery interface requires a proof against the application-selected
contract and retains actual effect history. Connecting all concrete contracts
to the mandatory dispatcher, preserving original saved replies for every
operation and enforcing the same boundaries in Rust remain required parts of
the task. This numerical change alone does not establish those guarantees.

## Verification

The focused tests cover an exactly completed cycle and a real two-state
repetition. An isolated MCP session checks propagation, review rollback,
truthful reporting of an earlier defeat edge, and rollback of a deletion that
encounters the same unfinished cycle. The existing inference tests cover the
acyclic calculation. No test uses a live account or downloads a model.
