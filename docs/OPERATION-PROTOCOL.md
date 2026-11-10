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
its original completed answer. Cancelling unfinished work preserves earlier
changes and answers and revokes permission for later publication. A cancel
request can run while another request on the same MCP connection is waiting
for embedding. The server drops its registered execution bodies, stops and
reaps their active native workers, and waits for their stop receipts before
replying with `worker_cleanup: confirmed_for_this_server`.

That confirmation covers this server's registered work. Another server sees
the database revocation, but its worker's exit is not confirmed by this reply.
An `operation_outcome` response reports
`worker_cleanup: not_confirmed_by_this_receipt`: reading a database fact alone
does not establish worker cleanup. If cancellation cannot be saved, this
server keeps its local work stopped and asks the caller to read the outcome
and retry cancellation with the original token. It does not restart the work.

MCP replies may arrive in a different order from requests. Each reply retains
its original request ID; response frames are written without interleaving.
Closing the connection drops every active request and its owned worker before
the server returns.

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
