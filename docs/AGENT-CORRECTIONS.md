# Helping an agent correct a request

When a request needs correction before any business data is written, return a
normal tool result with `status: "needs_input"`. Explain the problem, identify
its location, describe what is expected and suggest a correction. The result
does not say that the requested operation succeeded.

The common response is `mimir_core::interaction::NeedsInput`. Both the MCP
server and judge can use the same type. It contains:

- `status`: always `needs_input`.
- `business_changes`: always `none`, certified before emission.
- `next_action`: `correct_request_or_ask_user`.
- `message`: a plain-English instruction to correct the fields and retry, or
  ask the user for a value that is not known.
- `issues`: every reported problem, without a count or text-length quota.

Each issue includes `location`, a `fault` with its path, code and explanation,
the `expected` input, and a `suggested_correction`. `location: "request"` means
the path starts at the complete MCP request message. `location: "arguments"`
means it starts inside `params.arguments`. Array indices remain explicit path
components. For example, `["items", 2, "source_ref"]` identifies the third
item's source reference; it is not a dotted string that requires guessing how
to split a field name.

For a missing required project value, an issue can say:

```json
{
  "location": "arguments",
  "fault": {
    "path": ["project"],
    "code": "missing_field",
    "message": "A required field is missing."
  },
  "expected": "The actual project name for this work.",
  "suggested_correction": "Provide the missing value from the task context. If it is not known, ask the user; do not invent a value."
}
```

This example applies when the tool requires that field. It does not make
project mandatory for tools where it is optional. An unknown field is reported
with `unknown_field`, its exact path, the complete advertised field list and an
instruction to remove it or use the correct field while preserving the user's
meaning. The response never fills a missing value with a fabricated project,
identifier, zero, empty string or placeholder request.

A response must name at least one issue and provide a nonblank explanation,
expected input and suggested correction. These requirements make the response
actionable; they do not bound request size, text length or the number of issues.
The shared decoder rejects an incomplete response or an unknown
`business_changes` value instead of assuming that nothing changed. A decoded
remote claim is not itself proof about the remote database.

Only use this response after establishing that business data is unchanged.
`McpErrors.AgentCorrection.Certified` requires that equality before its response
can be emitted. Do not convert an arbitrary database or transport exception
into a correction because its message resembles a validation error. An
uncertain write requires outcome readback first. Saved operation metadata and
private diagnostics are distinct from publishing a belief or other business
data.

This is the shared response from #75. Routing malformed, missing, incorrectly
typed and unknown fields through it remains #80–#82, and continuing the judge's
correction dialogue remains #100. Defining the response does not claim those
call paths are already connected.
