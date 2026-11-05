# Pending work in judge batches

Every prepared judge batch must contain only work that still needs a review.
An item's reviewed source revision must be older than its current source
revision, and its ID must be absent from this batch's exclusion list. For
example, an already-reviewed experience A and an excluded experience B cannot
be handed to the model as new work.

[ExperiencePending](../spec/Mimir/ExperiencePending.agda) proves this for the
actual [pending query](../spec/Mimir/ExperienceRead.agda). Filtering establishes
the rule. Ordering, taking the requested limit and projecting stored rows into
public snapshots preserve it. `publicQueryEligible` carries the result through
the complete [public query protocol](../spec/Mimir/LearningQueryProtocol.agda),
including invalid limits and failed reads.

The [public output](../spec/Mimir/ApplicationOutput.agda) formats the selected
snapshots as an array. The judge's existing
[service binding](../spec/Mimir/JudgeBatchServiceBinding.agda) reads that array
with the actual snapshot decoder and passes its result to
[batch admission](../spec/Mimir/JudgeSelection.agda). Admission now applies the
full [pending and exclusion check](../spec/Mimir/PendingSelection.agda), after
decoding. This avoids relying on a remote reply's claim that its contents are
eligible. Syntax, shape and decoding failures keep their existing errors.

An already-reviewed or excluded item makes the entire reply malformed. The
list is not shortened to conceal the invalid item. `invalidReplyCannotPrepare`
proves that invalid input cannot produce a prepared batch;
`admittedReplyPreserved` proves that accepted input retains its exact list and
retained deferrals. The existing size, uniqueness, counter and project checks
still apply.

`completedSelectionIsEligible` covers every completed selection from retained
deferral reads through reconciliation and the pending request. Its prepared
result carries the checked pending and exclusion evidence. The exclusion list
is derived from that result's retained deferrals, as it is in the request.
The workflow can allocate a model trace only after receiving this prepared
result. Failed selection and malformed replies follow the existing failure
path instead.

This is an application-level admission and preservation proof. It does not
implement JSON parsing or prove library internals, and it does not claim a
native implementation correspondence. Selection describes the state observed
by its query; later source changes are handled by the existing pinned-review
and confirmation rules.
