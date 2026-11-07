# Complete request content

Valid input is kept in full. Source text, source references, actors, evidence
lists, extracted items, candidate declarations and review coverage have no
application text-length or item-count quota. Required content, exact quotations,
recorded actors, unique identities and valid references are still checked.

The remaining advertised provenance-reference ceiling of 2,048 characters is
removed. A new additive migration also removes the database's historical
128-character candidate-key ceiling. Candidate keys must still be nonempty.
The historical migration remains unchanged; existing databases receive the
new constraint through the normal migration mechanism.

An isolated PostgreSQL check publishes a candidate with its complete longer
key, retries it and verifies the original identity. Existing large-review
checks exercise 65 source records, long actor and source fields, long quoted
text and a review exceeding 64 KiB, while still refusing incorrect quotations
and duplicate sources. No request is shortened to fit an old quota.

This is #106's content and collection scope. Result selection, transport
framing, provider requests, diagnostics and storage retention have separate
issues. This source change does not run a live migration or install a binary.
