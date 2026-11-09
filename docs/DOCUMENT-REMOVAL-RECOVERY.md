# Retrying document removal

The registered removal operation removes the document's chunks, their vectors
and their grounding contributions. It recalculates the affected surviving
beliefs and commits those changes with the original removed-chunk count.
Unrelated documents and beliefs are preserved.

If saving completion fails, all of those changes roll back. If the commit
succeeds but its reply is lost, repeating the operation returns the saved
count. It does not remove a document subsequently loaded under the same path.
An explicit cancellation prevents publication and leaves the data intact.

Path preparation retains the original argument and the server-resolved path
separately. For example, `notes/latest.md` might resolve to `notes/week-1.md`.
The token keeps that resolution even if the symlink later points elsewhere.
The existing rule for a missing file is preserved: use the exact supplied path
when canonicalization fails. The calling agent cannot choose a replacement
resolved path as a public request option.

If the saved request or its required preparation is invalid, the response
explains what is missing. It asks the user whether to cancel the unfinished
token and reserve corrected work. It does not automatically cancel work,
replace the original binding, or invent a path.

The formal goal describes removal from the complete stored world, all required
posterior equations, preservation of other data, and the original public answer.
The shared recovery proof includes an interrupted commit with a lost reply.
Filesystem path conversion remains the existing external dependency; this adds
no path parser or low-level filesystem proof. Actual symlink preparation and
retry are checked against the implementation.

This slice supplies the registered storage/service entrypoints and concrete
recovery certificate. Mandatory public dispatcher and token admission remain
under #74/#76 and #85–#86. Server-owned path preparation must remain part of that
admission; it must not become a caller-controlled setting.
