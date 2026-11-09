# PostgreSQL-issued pattern metadata

The production `add_pattern` and `add_pattern_in_project` methods now ask
PostgreSQL for the UUID and creation time. They construct the pattern with those
exact returned values and publish it in that same transaction. The scoped MCP
`insert_pattern` path uses this service method as well.

The creation time is PostgreSQL's transaction timestamp. The UUID comes from
`pg_catalog.gen_random_uuid()`. The application neither generates a replacement
nor changes either value before returning and storing the pattern. Value
validation happens before this operation; invalid success rates create no row.

`GraphMutationProtocol.newIdentityAndTime` is the existing external metadata
boundary. UUID generation and uniqueness are PostgreSQL guarantees; this change
does not attempt to prove the generator or describe its implementation.

Disposable database checks require the stored creation time to equal the actual
publication transaction timestamp, exercise both service entrypoints and compare
their returned patterns with the stored rows. Unrelated patterns survive and
invalid values publish nothing. The low-level insertion method still accepts
explicit identities for reconstruction and isolated fixtures.

This fixes the production identity source. Registered pattern publication and
its saved-token retry proof remain under #136. It adds no public request fields,
limit, migration, installation or deployment.
