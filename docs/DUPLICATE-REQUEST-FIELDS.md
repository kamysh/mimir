# Repeated request fields

A request with a repeated field needs a correction before it can run. For
example, two `project` values cannot choose which project to delete. The
response names each repeated field, explains the ambiguity and asks the caller
to send one intended value. Even identical repeated values are rejected.

Paths include the complete nesting and array position, for example
`params.arguments.experience.source_records[0].actor`. Repeated request IDs
produce a response with a null ID; Mimir does not choose either supplied ID.
A unique valid ID is preserved. Messages without an ID receive no response;
their diagnostic goes to the application log and they execute no business work.
The corrected request can use the same connection.

Serde owns JSON syntax and scalar decoding. Mimir uses its visitor interface
to record repeated members before map insertion can hide them. Routing starts
only after the whole input is valid and the repeated-field list is empty.
No replacement parser, field-name guess, truncation or timeout is introduced.

The existing envelope model checks fields before object normalization. Its
general admission law says every admitted request has no repeated field at any
depth. The field-preserving library boundary is separate from ordinary map
decoding. This does not claim a proof of the JSON library's parser.

Native checks cover nested arrays, equal repeated values, repeated IDs, normal
scalar decoding and continued use of the actual server process. The process
fixture stores both possible projects and checks that both survive ambiguous
deletion requests. No installed binary, account or live database is used.
