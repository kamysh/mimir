# MCP message corrections

Message admission happens before tool dispatch. Each nonblank input line must
contain one UTF-8 JSON object with `jsonrpc: "2.0"` and a string `method`.
Supplied `params` must be an object; an omitted member is allowed at this layer.
Method-specific required fields are checked separately.

Requests carry a client-chosen string or JSON-number ID. Zero, negative and
fractional numeric IDs and empty string IDs are accepted. Null, booleans, arrays
and objects are invalid IDs. A usable request ID is preserved in a correction;
when no usable identity can be determined, the error identity is null.

Malformed encoding or JSON receives error `-32700`; an invalid envelope receives
`-32600`; otherwise valid envelopes with invalid named parameters receive
`-32602`. Error data contains the shared `needs_input` response, including each
field path, explanation, expected input and suggested correction. No business
handler runs for these messages. The connection accepts the next corrected
request after the response is flushed. Transport read/write failures still
terminate the broken connection.

A message without an ID is a notification. Notifications never execute request
methods such as `tools/call` and receive no response. If one appears to request
tool execution or contains malformed parameters, its correction is recorded in
the configured application log. The client must send an identified request to
obtain execution and a response. `notifications/initialized` remains supported.

The existing JSON library supplies syntax and encoding behavior. Duplicate
field detection before object normalization is a separate tracked change;
this admission layer does not claim to recover fields already discarded by
that decoder. Tool-argument admission is described in
[argument corrections](MCP-ARGUMENT-CORRECTIONS.md). The judge's correction
dialogue remains a separate follow-up issue.

The Agda exchange proves that rejected input can only serialize/write/flush its
correction, with no business-handler effect. It also proves that notification
dispatch has no effects. A native process test attempts project deletion through
invalid envelopes and notifications, then retrieves the original data through
the same server connection.
