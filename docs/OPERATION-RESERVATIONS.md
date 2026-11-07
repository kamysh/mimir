# PostgreSQL-issued operation tokens

The storage API can reserve an operation token before business publication.
`reserve_operation` returns `operation_token` and `reserved_at` directly from
PostgreSQL. The insert supplies neither value; the database uses its UUID and
timestamp defaults. UUID allocation is an external database guarantee.

The caller retains the returned token. `read_operation_reservation` looks up
that exact token and returns the stored reservation or absence. It does not
create a replacement token, infer an identity, retry automatically or filter
by age. Reserving another token does not expire an earlier one.

Reservation changes only `mimir_operation_reservations`. It creates no belief,
experience, vector or other business record. The additive migration creates
that metadata table; it does not change historical migrations. The existing
transaction and migration receipt rules still govern publication.

This storage foundation adds no MCP tool or CLI command. Saved results,
atomic saved steps and client integration remain #121–#123 and
#85–#86. A reservation alone does not yet guard a business handler or establish
that all operations recover correctly. Public reservation-control recovery is
also an obligation of #163.

The Agda reservation model proves readback of a published token and preservation
of the complete business state for every transaction receipt, including both
possible states after a lost acknowledgement. It contains no identity
generator or UUID uniqueness proof.

Isolated PostgreSQL verification checks persistence across a new service
connection, continued readback of old reservations, absence after rollback and
unchanged contents of every business table, including graph and vector data.

## Keeping the original request

After the calling interface validates a request, `bind_operation_request`
stores its operation name, arguments and relevant settings under the reserved
token. PostgreSQL supplies the binding timestamp. A binding is metadata, not a
receipt that a belief, document or other business record was published.

For example, a token first bound to deleting project A cannot later be used to
delete project B. A changed operation, argument or captured setting returns
`ChangedRequest` with the complete original binding. The caller must read that
binding and retain its original request, or explicitly resolve the old operation
before starting distinct work. The method never overwrites the earlier request
or allocates another token to hide it. `read_operation_binding` supplies the
same readback after reconnecting or losing a reply.

Request comparison uses PostgreSQL JSONB equality. Object-key order and
equivalent numbers do not change the request; array order does. No application
hash, truncation, expiry, retry delay or size limit is involved. The database
also rejects updates and deletes of an existing binding. Competing clients
cannot bind different requests successfully under one token.

The caller supplies only the settings that govern the admitted operation;
interface-specific capture belongs to #85–#86. Credentials are not operation
policy. This storage-shape constructor does not replace tool-schema validation,
and no public MCP/CLI handler is enabled by this change.

The binding model states that an existing request remains unchanged after any
transaction receipt, including a lost acknowledgement, and that binding changes
no business data. These are storage guarantees; completed business work still
requires its own atomic step and saved result.
