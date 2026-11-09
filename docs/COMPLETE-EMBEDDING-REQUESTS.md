# Complete embedding requests

Mimir sends the complete collection of submitted texts to its owned embedding
worker. It has no configurable group allowance and never uses zero to mean
something else. An empty collection returns an empty result without loading a
model. Each nonempty text still undergoes the approved check against the
configured model's declared capacity; it is never silently shortened.

`embeddings.batch_size` and the `mimir init batch_size=...` argument are retired.
An old setting requires correction, including zero, positive values and values
of the wrong type. Configuration checking names the setting and gives the
repair command. Run `mimir config upgrade` on the intended configuration, then
`mimir config check`. Upgrading removes that setting and preserves unrelated
settings and comments. It chooses no replacement limit.

Cancellation still belongs to the calling job. Stopping a call terminates and
reaps its owned native worker, including when model computation is blocked.
Completing the request does not create a timer or a detached task.

The private worker protocol is version 2 and no longer has a batch-size field.
Both shipped binaries implement it. SDK users selecting a worker executable
must use the matching binary; private protocol mismatches remain explicit.
This does not change the public MCP tool list or introduce a request override.

The formal model passes the entire nonempty collection to tokenization at
once. Its cancellation transitions remain available during loading, inference
and joining. Provider response count, index and dimension checks remain in
place; they describe whether a returned vector belongs to its input, rather
than limiting how much work may be requested.
