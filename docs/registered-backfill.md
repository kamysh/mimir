# Registered backfill checkpoint

The internal `reembed_operation` path keeps the original selected beliefs and
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

This is part of issue #147. Focused native tests verify the behavior above, and
Agda checks the item policy, original-plan admission and complete-selection
requirements. The proof covering every interruption across capture and the
repeated body remains unfinished. Public CLI/MCP token routing is separate work;
the existing `mimir reembed` command does not yet use this internal path.
