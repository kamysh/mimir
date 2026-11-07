# Required fields and input shapes

Each registered MCP tool checks its supplied arguments against the required
fields and JSON shapes in its actual advertised input schema before calling its
business handler. This applies to ordinary callers and the judge because both
use that registered dispatcher.

Missing fields and incorrect types return `needs_input` as ordinary tool
content. The response identifies each field, including array indices and nested
record fields, explains what is required and asks the agent to correct the
request or ask the user. It certifies no business changes. For example,
`delete_project` with `project: false` asks for the intended project string;
`query_relevant` with `limit: "10"` does not silently select a default or call
the embedding provider.

Omitting `tools/call.params.name` or supplying a non-string name receives a
JSON-RPC invalid-parameters response with the same correction details. Supplied
`arguments` must be an object. Omitting arguments supplies the protocol's empty
object, after which the tool's required fields are still checked.

The checker covers objects, arrays and their elements, strings, numbers,
integers, booleans, explicit null alternatives, required fields, declared enum
values and constant branch tags. Declared alternatives are checked without
choosing missing values. It imposes no size, issue-count, time or work limit.
Existing advertised defaults still apply to omitted optional values; the
restriction-removal issues own those defaults. Invalid supplied values never
become omission through this checker.

This is field admission, not a complete JSON Schema validator. Unknown fields
are checked as described in [unknown fields](MCP-UNKNOWN-FIELDS.md). Numeric ranges, reference validity, revision conflicts and other
business conditions retain their separate checks and follow-up issues. No
claim is made here that every later refusal already uses the correction
dialogue. The native/model binding work remains #85 and #91, and schema
alignment remains #102.

The existing Agda decoder now requires an argument object and checks supplied
optional field types before legacy fallback accessors. A general theorem shows
that a rejected supplied value prevents request decoding. MCP method admission
also rejects missing names and malformed argument objects before dispatch.
Native process verification sends malformed calls, then successfully reads
retained data over the same connection.
