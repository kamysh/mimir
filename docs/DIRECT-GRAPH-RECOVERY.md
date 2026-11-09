# Retrying pattern and relationship writes

A pattern write now has a registered entry that commits the pattern and its
complete original answer together. PostgreSQL assigns the pattern's UUID and
creation time inside that transaction. If a reply is lost, the same operation
token returns the saved pattern, including those original values. It does not
create a second pattern.

Support and cause writes add exactly the requested relationship. A contradiction
adds both directions in one transaction. Repeating a token returns its original
`{"ok":true}` answer without adding another relationship. A distinct operation
token still represents a separate requested write; this change does not silently
merge distinct requests.

The registered entries decode the original stored request, reject unknown fields,
check weights, and require existing belief endpoints. A refused request explains
what needs correcting and how to obtain the intended values. Neither the graph
nor a completed answer is saved for that refusal. A confirmed rollback leaves
the publication pending. If a commit or rollback cannot be confirmed, the caller
must read the original token's saved outcome before deciding what to do next.

`DirectGraphRecovery` derives the added relationships from the original request
and complete stored world. Its recovery instances preserve all other records and
the original answer after interruption. `PatternPublicationRecovery` has a public
input containing only the operation token. The new pattern's identity and time
arrive in the committing transaction's effect reply and are used by its physical
publication relation. Its convergence proof allows a different external reply on
retry and proves that the committed pattern and answer still remain unchanged.
The proof includes both possible outcomes of a lost commit acknowledgement.
PostgreSQL's UUID generator, clock and scalar formatting remain external
dependencies; this does not attempt to reimplement or prove them.

The mandatory public dispatcher remains the separate work in #74. It must use
these registered entries and concrete recovery instances. This change introduces
no MCP tools, request fields, background work or application limits.
