# Pattern deletion and its original answer

The registered `delete_pattern` step reads the pattern ID from its saved request.
Deleting the node and its edges, retiring its review candidate, and saving both
answers happen in one PostgreSQL transaction. A later call with the same token
reads the original answer. If the pattern existed, that answer remains
`{"deleted":true}` even though the node is now absent.

The two saved answers are the registered step key
`["store.delete_pattern",null]` and `@operation-result`. A partial pair from an
older operation requires reading and resolving the original receipts; it never
authorizes repeating the deletion or inventing the missing answer. The helper
checks the original request before consulting those receipts.

`GraphDeletion.PatternRecovery` states the desired result on the complete
application world. It removes the chosen identity and its references and retires
its candidate while preserving history, documents, vectors and unrelated rows.
The shared `Recovery.StoreFinalStep` uses the actual operation journal and proves
that retrying after any interruption, including a committed transaction whose
reply was lost, reaches that original world and answer. It also requires the two
stored answers to be published together. A partial pair produces a recovery
decision and preserves the whole world.

This is the registered storage operation and its proof. Public MCP and CLI token
admission, belief deletion, and the mandatory top-level proof-backed dispatcher
remain separate issues. Existing raw callers continue to use the same deletion
transaction body until those interfaces are connected.
