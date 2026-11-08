# Pending experience selection

`pending_experiences` returns all matching pending experiences when `limit` is
omitted. A supplied `limit` is a positive integer. Zero, negative, fractional,
string and null values require a correction; zero never means all.

The project filter and `exclude_ids` still apply before selection. Results keep
their established update-time and identity order. Selecting rows does not claim,
review or remove them. A filtered empty result does not establish that a project
has no deferred work.

Core callers use `Option<NonZeroUsize>` for the count. The database read does not
apply an implicit result ceiling or narrow a supplied count to a signed database
integer. Explicit positive selection is applied to the ordered result.

The existing formal pending-query model distinguishes omission from a positive
count. Its eligibility laws cover both paths. Wire admission explains invalid
counts before the query can run.

This addresses #229 under #103. Removing the judge's own `batch_size` quota is
separate work in #162; until then the judge still sends its explicit count.
