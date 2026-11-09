# Reporting actual backfill work

Embedding an existing belief succeeds only after the configured backend returns
exactly one usable vector and the database acknowledges its write. No backend,
an empty response, multiple vectors, or an empty, nonfinite or zero vector
requests a user decision before any vector write. None counts as embedded.

When a CLI backfill cannot continue, it reports the confirmed prior writes,
their count, the skipped count and the current belief separately. A failure
does not print the completed-run summary. If the current write's outcome is
unconfirmed, the response requires readback before retrying and does not claim
rollback or successful publication. Previously confirmed work remains visible.
The caller must open the user dialog using the reported cause and repair path.

The general formal law requires every successful embedding trace to contain
one usable vector and its acknowledged write. The storage binding associates
that acknowledgement with the actual committed vector update. An empty backend
response has no route into the successful branch that increments the count.

Three PostgreSQL tests cover absent/invalid responses, actual vector storage
and provider failure preserving an existing vector. A real CLI invocation
checks missing configuration and its normal correction response. These checks
use a disposable database and fixed providers, without a model or account.

This is a prerequisite within #147. Durable capture of the original pending
selection, registered per-item replay, model binding, original aggregate
counts and the complete re-embedding recovery instance remain unfinished.
The current fix must not be described as completion of #147.
