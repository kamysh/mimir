# Read-only intervention outcomes

`query_intervention` asks what probabilities would follow from setting a chosen
belief to a given probability. It does not store that change. Its selected
causal descendants, priors, review contributions and document grounding come
from one application snapshot.

`InferenceStorageBinding.InterventionRecovery` supplies the concrete recovery
instance. Its goal is fixed to `NumericalOutcome.Goal`, independently of the
calculation implementation. A successful result must contain every selected
posterior, satisfy every final posterior equation and return the corresponding
projected probabilities. There is no iteration count or accuracy allowance.

The calculator supplies an untrusted report. The existing checker validates the
complete result or replays its reported sweeps. A rejected report is identified
as such, with evidence that the actual report failed validation. An observed
repetition carries the replay and the unsatisfied final equation condition.
Neither outcome publishes posteriors or claims a completed projection.

The general recovery proof covers every interruption in the shared execution
relation, including a lost reply. The preservation theorem compares the whole
application world: stored probabilities, graph edges, documents, vectors,
learning history, embedding owners and operation receipts all remain unchanged.
The implementation is not assumed to calculate correctly; accepted reports owe
the checked equations and exact selected identities.

This supplies the instance for the mandatory operation table. Connecting that
table as the only top-level dispatcher remains #74 and #76. It introduces no
new calculation implementation, timeout, model assumption or live change.
