# Registered backfill

The CLI `reembed --operation-token UUID` path keeps the original selected beliefs and
model settings. Each vector and its saved item answer commit together. The last
item also commits the original embedded/skipped totals. A retry reads those
answers instead of repeating completed embedding work or selecting new beliefs.

If another call creates a vector for unchanged source text, the redundant owned
embedding stops on the database event, preserves that vector, records a skipped
item and continues. Product deletion and explicit cancellation also stop owned
work through database events. No polling timer or deadline is added.

An unfinished operation must recheck its whole original selection. For example,
if A was embedded, B failed, and A was then deleted, retrying cannot report a
completed backfill. It asks for a user decision and preserves A's original
receipt. The same rule covers an initially skipped belief whose source or vector
was removed. A late final result rolls back with its vector and item answer.

An operation that already completed returns its original saved answer, even
after a later deletion or configuration change. It does not recreate deleted
beliefs or vectors.

The Agda recovery certificate covers binding the original model, reading the
source snapshot, saving its plan and committing every vector and answer. A
completed retry must preserve unrelated records and original saved answers.
The first completion requires the whole original selection to be complete and
the saved totals to match the item answers. A stopped preparation cannot claim
successful embedding.

Focused native tests check the database changes and event-driven cancellation.
Reserve the action with `mimir operation reserve REQUEST_KEY`, then use its
returned token with `mimir reembed --operation-token UUID`. Preserve both across
retries; omitted tokens produce correction guidance before configuration is
loaded. Use `mimir operation outcome --operation-token UUID` to inspect progress.
