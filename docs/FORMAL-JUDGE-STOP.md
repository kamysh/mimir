# Stopping the judge

When judge work stops, its owned work must stop as well, including any active
embedding. A stop request alone is not confirmation that the work has stopped.
Changes already committed remain committed.

[JudgeMcpLifecycle](../spec/Mimir/JudgeMcpLifecycle.agda) describes the current
client cancellation obligations. The specification does not yet connect the
stop guarantee to every operation.
