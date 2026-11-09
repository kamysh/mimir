# Complete JSON input and useful corrections

Mimir reads complete JSON requests without a fixed nesting-depth allowance.
Malformed JSON still gets a syntax diagnosis. A valid JSON request with missing,
unknown or wrongly typed fields gets an explanation and a suggested correction.
The caller can repair the request and continue on the same MCP connection.

For example, a nested array supplied as `limit` is still the wrong type. Mimir
explains that the caller must either supply a positive count or omit the field
to request all matches. It does not reinterpret zero or replace bad input with
an invented default. Duplicate MCP fields are rejected rather than choosing one
of their values.

The same JSON adapter is used for judge responses, stored request metadata and
saved answers. Large nested values can be read, written, copied, formatted and
released safely, including after a parse error or when queued work is dropped.
The standard JSON parser remains responsible for JSON syntax; `serde_stacker`
grows the stack as needed. The adapter's owned document type handles tree cleanup
and copying without recursive calls. No text is truncated and no depth quota is
substituted for the removed parser guard.

Verification includes 10,000-level object/array inputs, malformed suffixes,
repeated fields, judge history and queued work, and an actual MCP session that
continues after corrections. PostgreSQL metadata and saved answers are checked
by a separate disposable-database test. This JSON change does not claim to remove
the separate TOML parser guard; that remains tracked in #160.
