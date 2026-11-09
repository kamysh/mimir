# Recovering an operation reservation

The local storage API requires `request_key` when reserving an operation. Keep
one exact key for one action and repeat it after a lost response. For example,
`mimir:delete-project:case-125` returns the same PostgreSQL-issued token and
reservation time on every retry, including after reconnecting.

An empty or blank key is rejected with instructions to supply and reuse a
stable name. Keys are compared exactly; they are not trimmed or renamed.
There is no default key, expiry or automatic replacement. A different key is
a different action, never a way to bypass an unresolved earlier operation.
The key does not replace validation of the operation's arguments and settings.

The database publishes the key and reservation in one transaction. Concurrent
calls recover the same reservation; a losing allocation is rolled back.
Failed key publication leaves neither a key nor an extra reservation.
Database guards preserve the original association, token and time. Existing
reservations created before keys were introduced remain readable by their
original token; the migration does not invent keys for them.

Reservation metadata changes no belief, document, vector or learning record.
The source migration is additive. This prerequisite changes the local core
API; public control tools and their required dispatch proofs remain in #163.
No live migration or installation is part of #200.
