# Belief listing selection

`list_beliefs` returns every matching belief when `limit` is omitted. Project
and memory filters still apply. Supplying a positive integer requests a page
of at most that many beliefs, ordered by creation time and identity. There is
no ten-record ceiling or hidden default page size.

A page returns `beliefs`, `total`, `offset` and `next_offset`. Use `next_offset`
to continue. `offset` starts at zero and requires an explicit positive limit.
The total and page remain separate database observations, so concurrent changes
can affect them independently.

For example, if thirteen beliefs match, `limit: 12` returns twelve and points
to the next page. Omitting the limit returns all thirteen. `limit: 0` returns a
structured correction explaining that a positive integer selects a page and
omission selects all matches. The agent can correct the request on the same
connection; it should not guess a replacement count.

Page selection uses exact numeric comparisons in PostgreSQL, so a large
positive selection or offset does not acquire an extra limit from the SQL
`LIMIT`/`OFFSET` integer representation. The request's host integer
representation is checked during decoding; values are never rounded or
silently narrowed.

This change covers belief listing in #198. Other retrieval and learning
defaults remain tracked by #103, and CLI selection remains #105.
