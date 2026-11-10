# Writes, retries and saved answers

Before an MCP write, call `reserve_operation` with a nonblank `request_key`
that identifies this intended action. Keep that key. PostgreSQL returns
`operation_token` and `reserved_at`; reservation alone changes no belief,
document or experience. If its reply is lost, repeat the same key to recover
the original token and time. A separate action needs a separate key.

Supply that token in the write's required `operation_token` field. The server
checks the input, then keeps the original tool name, argument fields and
server-selected settings. Retry the same tool with the same fields and values.
Adding a previously omitted field changes the request, even if its value looks
like a default. Object member order does not change the request.

For example, reserve an action before inserting a pattern. Supply the returned
token with its situation, approach, success rate and optional project. If the
reply is lost, repeat those same arguments and token: the original pattern and
answer are returned. Changing the approach under that token asks for a
correction; it does not create another pattern.

Basic input errors are corrected before a new request is bound, so the caller
can correct them using the same reserved token. After admission, a missing or
changed prerequisite can still need a user decision. Keep the bound request;
do not replace its arguments, silently choose another model or invent a new
action to bypass the problem.

Call `operation_outcome` with the token to inspect its saved state:

| Status | Meaning |
| --- | --- |
| `reserved` | The token exists; no business request is bound yet. |
| `pending` | The original request is bound but lacks a final answer. Where available, the reply includes its saved answers and next step. |
| `completed` | `result` is the original saved business answer. Retrying does not repeat the changes. |
| `cancelled` | Further publication under this token is blocked; committed changes and saved answers remain. |
| `needs_input` | The shared correction response explains the problem, expected input and suggested repair. Discuss an uncertain choice with the user. |

Successful write responses and outcome readback use the same saved-outcome
format. `original_request` contains the token, binding time and a `request`
with its tool name, `arguments` and captured `settings`. The settings are
readback information; they are not extra fields to send to the business tool.
The tool schema describes the accepted arguments. Read-only business tools
keep their existing responses and need no operation token.

Completed answers are read before checking today's model, retirement policy or
source file. Unfinished work retains its original settings and preparation;
a conflict explains how to restore its prerequisite or discuss cancellation.
The server never infers completion from one saved step.

Only an explicit user decision invokes `cancel_operation`. The judge must not
cancel automatically to escape a problem. Cancelling completed work returns
its original completed answer after stopping any duplicate work still running
under that token. It adds no cancellation row or repeated business mutation.
Cancelling unfinished work preserves earlier
changes and answers and revokes permission for later publication. A cancel
request can run while another request on the same MCP connection is waiting
for embedding. Every copy registers its execution in PostgreSQL before its
body or provider starts. One enclosing public request owns its provider
children through a private request-specific capability and joins their stop
receipts before acknowledging that request. It does not infer ownership from
another call using the same token. Standalone provider work registers its own
execution. Cancellation stops the registered bodies, stops and
reaps their active native workers, and waits for every copy's saved stop
acknowledgement before replying with
`worker_cleanup: confirmed_for_all_registered_copies`.

For example, if two Mimir servers are embedding under the same token, cancelling
through either waits for both. A disconnected or crashed copy without an
acknowledgement leaves confirmation pending. There is no expiry, heartbeat,
retry quota or timeout that turns missing evidence into success. Original
completed answers and earlier committed changes remain intact.
If the operating system cannot confirm that a local worker exited, the reply
instead says `worker_cleanup: unconfirmed_for_this_server` and
`next_action: open_user_dialog`. It includes the worker's process ID, private
diagnostic directory and complete error. The caller must explain the unresolved
cleanup before starting replacement work. Retrying cancellation with the same
token checks for an exit receipt; it does not erase saved answers or repeat
earlier business changes. Diagnostics and partial downloads remain available
while cleanup is unconfirmed.
An `operation_outcome` response reports
`worker_cleanup: not_confirmed_by_this_receipt`: reading a database fact alone
does not establish worker cleanup. Its complete `pending_executions` list
identifies every copy still lacking a saved stop acknowledgement. The cancel
call can remain waiting while another request reads this state. If cancellation cannot be saved, this
server keeps its local work stopped and asks the caller to read the outcome
and retry cancellation with the original token. It does not restart the work.

The list includes `owner_program`, `owner_pid`, `owner_host`,
`owner_host_source`, and `client_address`. The address is what PostgreSQL
actually observed; a proxy or container network can make it different from
the address supplied by the client. Linux host identity comes from the complete
kernel hostname. An environment-only hint is labelled as such; missing identity
is reported as null. Use these fields to find the program needing attention.
They never prove that it stopped, and Mimir does not guess its log destination.
Explicit outcome readback includes this information even after the business
result completed, while ordinary completed write/replay answers remain unchanged.

MCP replies may arrive in a different order from requests. Each reply retains
its original request ID; response frames are written without interleaving.
Closing the connection drops every active request and attempts to stop and reap
its owned worker. The host then owns the acknowledgement writes; it does not
detach cleanup and claim it finished. A cleanup or acknowledgement error is
retained in private diagnostics; dropping the connection is not a confirmation
of successful cleanup.

All participating copies must be built with the compatible 2.3.0 registration protocol.
Stop or upgrade older copies before relying on global confirmation: an old
binary that never registered cannot be discovered by an empty execution query.
A version string alone is insufficient if a build predates this protocol.
This confirms Mimir-owned work and local worker exit. It does not claim that
an independent hosted provider stopped computing after its HTTP request closed.

The CLI uses the same operation identity and saved-answer format. For example:

```sh
mimir operation reserve forget-my-project
# Keep the operation_token printed above, then supply it to the intended write:
mimir forget my-project --operation-token UUID
mimir operation outcome --operation-token UUID
```

Use the returned UUID in place of `UUID`. If the reservation reply is lost,
repeat `mimir operation reserve forget-my-project` to recover the same token.
If the write reply is lost, repeat the exact write with that token. Every CLI
database write requires this flag, including document indexing, evidence,
decay, sweeping and reembedding. Missing or malformed flags return correction
guidance before reading configuration or opening the database. Read-only
commands reject an unrelated operation token. `operation cancel` requires the
same flag and an explicit user decision.

The judge host supplies its review token; the reviewing model does not choose
one. The reservation key identifies the experience, its source revision and
the expected review revision. Retries and client restarts retain this same
action. A changed proposal cannot silently reserve replacement work. The
review tool shown to the model omits the host-owned field and the guidance
explains who supplies it. The model cannot call cancellation through the
judge's restricted tool list.

Source changes do not upgrade installed binaries or configuration by themselves.
