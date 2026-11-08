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

Relationship requests name a missing `from_id` or `to_id`; contradictions use
their advertised `id_a` and `id_b` names. Grounding requests name `chunk_id` or
`belief_id`, and intervention requests name `id`. These checks use the existing
transaction or read-only snapshot before a business write. The correction
suggests the relevant belief or document lookup and asks for a user decision
when the intended record is unknown. Both MCP and the corresponding CLI
commands preserve this guidance. An absent-record read still returns its
advertised absence result; deleting an already absent belief still returns
`deleted: false`.

An inner refusal is not enough to certify a larger operation. For example,
document loading can already have committed its document before automatic
grounding encounters a missing record. That error cannot be projected as
`business_changes: "none"` for the entire load. Only the checked atomic graph
requests and read-only intervention use the new stored-reference projection;
other learning conflicts retain their separate checks in #93.

Learning requests retain the exact position of each existing belief reference,
such as `experience.belief_ids[0]` or
`review.candidate_links[0].from.belief_id`. Missing beliefs, beliefs owned by a
different project, global beliefs and temporary working beliefs receive a
correction explaining the existing target rules. Assessment reads identify
`belief_id`. These responses suggest a lookup, require inspection of the
returned project and memory type, and ask the user when the intended reference
is unclear. They never move a belief or change its memory type to make a
request pass.

Existing review references are checked before embedding preparation and again
inside the publication transaction. A failed check leaves the source pending
without publishing a review or changing its acknowledgement. Missing or
wrong-project pattern references identify `experience.pattern_id` and suggest
`list_patterns`; project-owned patterns and permitted global patterns retain
their existing behavior. Candidate declarations and item-identity conflicts
remain separate parts of #93.

Item-identity corrections also preserve their exact position, such as
`experience.learning_items[1].id`, `review.extracted_items[0].actor` or
`review.assessments[0].item_keys[0]`. A new item needs a stable local key and
must omit its stored ID; PostgreSQL supplies that ID. A later key/ID pair must
match the original mapping, and its recorded source and actor remain immutable.
The response names the problem and tells the agent to read the original item
mapping before retrying. It never silently replaces an ID or creates another
observation to bypass a conflict.

The review preflight checks existing ownership and assessment item names before
embedding. The publication transaction repeats the checks and owns all new item
allocations. A later refusal rolls back every tentative owner with the source
or review; exact retries keep their assigned IDs. Locating an error does not
alter a successful normalization or its store. Database allocation errors and
unclassified failures remain errors, rather than claims of agent misuse.

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

`insert_belief` requires an embedding of the complete content and a supporting
passage from an indexed, compatible document before publication. Missing
configuration, embedding rejection, absent support or support removed before
publication returns this normal decision response with the cause and repair
instructions. The agent must open a dialog with the user. It must not invent
support, shorten the content, change the model or store an ungrounded belief
to bypass the decision. A successful publication stores all components in one
transaction.

The same requirement applies to new belief candidates in `review_experience`.
Every new candidate is prepared before any review is published. The response
names the candidate key and array position; argument issues retain their full
path under `review.candidates`. Experience citations alone do not satisfy the
indexed-document requirement. If any preparation fails, the whole review
remains pending. Existing completed reviews replay their original identities
without requiring another embedding call.

Preparation can reserve ownership metadata before asking for a decision. Its
formal response requires equality of the entire business snapshot, including
learning rows, documents, vectors, grounding and raw history. It may differ in
reserved operation/ownership metadata as explicitly allowed by the user. This
response condition does not narrow the recovery goal: recovery still compares
the complete application world and original reply.

The judge recognizes a complete `needs_input` response before checking the
ordinary result shape. For example, a misspelled field in a learning-context
query returns correction guidance, rather than an "invalid learning context"
failure caused by looking for search results in that response. The complete
guidance reaches the same agent conversation, which can correct and retry.
Correcting the same tool clears its pending correction. If the agent stops
while a decision is unresolved, the review remains pending with its complete
guidance in private diagnostics and public instructions to open the user dialog.
Other selected reviews continue. No invented value, automatic cancellation,
attempt limit or retry timer is used.

Revision conflicts also return an actionable correction when the request was
refused before publication. `record_experience` identifies `expected_revision`
and directs the agent to `get_experience` and, when needed, `experience_history`.
`review_experience` identifies either `review.experience_revision` or
`expected_review_revision`, and directs the agent to `get_experience` and
`get_learning_review`. The response includes the supplied and current values.
The agent must compare the current source or review with its intended change
before resubmitting; it must not blindly replace newer work or invent a token.
Exact retries of completed requests still return the original saved result.

Deleting a candidate after a review completes does not erase that review's
saved name-to-ID answer. An exact retry reconstructs the original mapping
without recreating the candidate, changing its deletion marker, reapplying
learning effects or appending review history. A new review still cannot reuse
a deleted candidate name. A missing or changed saved declaration remains a
readback error; the server never guesses an original ID.

These responses are emitted only for the identified revision checks. Internal
snapshot faults, ordinary database errors and uncertain commits do not become
corrections merely because their diagnostic mentions a revision. Both the
record and review projection laws preserve readback after a lost acknowledgement.

A database failure around publication can leave its outcome unknown. That
failure is not converted into `business_changes: "none"`. Read back the original
identity and saved operation outcome before deciding what to repeat.

Malformed UUID arguments use this response before a handler executes. For
example, `record_support` with `from_id: "not-a-uuid"` identifies `from_id`,
explains the accepted identifier and directs the agent to look up the intended
record or ask the user. Nested fields and list positions are identified in the
same way. Accepted UUID forms are preserved; validation does not rewrite the
request or invent a replacement ID. A correctly formed UUID whose record does
not exist is a separate stored-reference check.

When the tool schema requires nonempty text, an empty supplied value also
receives a correction before execution. For example, an empty candidate key
points to `review.candidates[0].key` and asks for the intended key or a user
decision. The response does not create a placeholder. This check adds no
maximum length and does not impose a new whitespace rule.

The shared response from #75 is used by MCP admission and the judge's correction
dialogue. Remaining stored-reference corrections, complete schema
parity and mandatory recovery dispatch retain their separate obligations in
#93, #102 and #74/#76. A response format alone does not establish those
properties.

The CLI also prints this JSON response and exits successfully when its request
needs correction before execution. Check `status` to distinguish a request for
input from completed work. Parser diagnostics retain their complete explanation
and usage, identify missing or unknown arguments, and give repair instructions.
Invalid identifiers and numeric values are checked before configuration is
loaded or a database connection is opened. For example, `mimir delete belief
bad-id` gives the same identifier diagnosis as MCP `delete_belief` with that ID;
`mimir list --limt 2` identifies the misspelled flag. The response does not guess
the intended value or silently replace an invalid value with a default.

Help and version requests retain their ordinary output. Operational failures
still return a failing exit status; they are not rewritten as a claim that
business data is unchanged. Valid command output is unchanged.
