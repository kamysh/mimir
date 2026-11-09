# Completing a defeat after interruption

Recording a defeat has two durable steps: add the requested edge, then
recalculate the affected beliefs. The first step does not mean the whole
operation succeeded. If the process stops between these steps, the edge and
its saved answer remain, but the operation is pending.

The registered storage operation resumes using its original token, arguments
and plan. It reads the saved first answer instead of inserting another edge.
The final step publishes every required posterior update and saves both the
step answer and the operation answer in one transaction. If saving that answer
fails, the posterior changes roll back; the previously committed edge remains.
If the final reply is lost, a retry returns the original saved answer.

When a calculation repeats distinct states and needs a user decision, the
response reports the committed edge, the pending operation token, and that no
posterior update or completion answer was saved. The calling agent must open
the dialog using the reported calculation details. It must keep the token and
read the outcome before resuming, rather than insert another defeat or claim
completion. Explicit cancellation preserves committed work and prevents later
writes under that token.

Standalone propagation follows the same final-publication rule. Its saved
answer is the original list of changed belief probabilities. A later retry
does not calculate a different answer from a subsequently changed graph.

The formal goal combines the requested edge contribution with the full
posterior equations and preservation of every other stored component. The
generic interruption relation includes every prefix and a commit whose reply
was lost, at each of the two actual boundaries. The standalone goal also fixes
the returned probability list. No expected result is supplied by the caller.

The PostgreSQL checks cover the committed first step, reconnect and retry,
completion-receipt rollback, cancellation, numerical decisions, invalid
original arguments and original result replay. A real MCP session checks that
a missing source receives correction guidance and a subsequent corrected call
works on the same connection.

These are registered storage entrypoints and concrete recovery certificates.
Mandatory public dispatcher and token admission are tracked in #74/#76 and
#85–#86. This change alone does not install or activate that integration.
