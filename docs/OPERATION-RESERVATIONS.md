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

This storage foundation adds no MCP tool or CLI command. Argument binding,
saved results, atomic saved steps and client integration remain #120–#123 and
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
