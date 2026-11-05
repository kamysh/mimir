# Competing review updates

Two reviewers can prepare different answers from the same review number. For
example, both may expect review 4. If one saves review 5, the other must read
that saved state after obtaining the shared lock. It can return an exact retry
or refuse the stale request; it cannot save a second update based on review 4.

[ReviewCompetition](../spec/Mimir/ReviewCompetition.agda) connects this rule to
the public review plan in
[LearningOperations](../spec/Mimir/LearningOperations.agda). Its proofs quantify
over both review payloads, the initial database state, candidate identities,
clocks, transaction handles, replies and outcomes. They use the actual plan's
validation and publication branches, including candidate, assessment, edge and
numeric changes. A fresh accepted proposal advances the target's review number
exactly once. A stale request cannot enter that publication branch.

The proof starts both programs at transaction begin. It obtains the first
operation's published state from its completed execution, then derives the
second operation's read from that state and the supplied READ COMMITTED
guarantee. It does not give the second classifier a caller-chosen stale or
updated read value. The final database state is the original state, the first
request's complete proposed state, or the second request's complete proposed
state. Both proposals are calculated from the original state, so the result
cannot combine two fresh updates that used the same old review number.

Begin, lock, read and write failures leave the published state unchanged. A
rejected commit does too. A lost commit acknowledgement retains both possible
database outcomes: unchanged or completely saved. If it saved, the later
reviewer sees the advanced counter; if it did not, the later reviewer can still
save. A fresh success requires an acknowledged commit. Failed cleanup is not
treated as evidence that the native lock has been released.

## Connection to the database

[LearningTransactionDatabase](../spec/Mimir/LearningTransactionDatabase.agda)
binds actual transaction effects to native observations. Its receipts retain
the handle, shared database/key lock, read event, uncommitted write set and
atomic publication outcome. The read is made before this transaction's own
writes. The completed public program also satisfies the independent
[transaction scope policy](../spec/Mimir/LearningTransaction.agda).

[NativeLockOrder](../spec/Mimir/NativeLockOrder.agda) uses the supplied exclusive
lock guarantee to show that two distinct holders' intervals cannot overlap.
The intervals belong to one native history and end when the database releases
the lock, including release caused by failure. Client reply times do not define
these intervals. `completeInNativeOrder` handles either resulting order and
requires the execution observations to use the same handles and acquisition
snapshots as that history. Failures before successful acquisition are covered
by the complete-program publication laws without requiring a lock interval.

PostgreSQL's atomic transactions, exclusive locks and READ COMMITTED visibility
are external guarantees. A native adapter must supply genuine observations on
the same handle and lock, preserve the complete write set, and relate the
ordered protected executions to its native history. This change supplies no
adapter instance and claims no implementation correspondence, scheduler model,
fairness or termination proof. It does not prove PostgreSQL internals.
