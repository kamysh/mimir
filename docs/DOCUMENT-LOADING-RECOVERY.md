# Complete document loading

The saved-operation path keeps the original document preparation before
embedding starts. This includes the resolved file path, complete source,
chunks, their PostgreSQL-issued identities, the original indexed chunks and
the owner of the embedding work. Retrying the same token uses this saved
preparation. Editing the file afterward does not change that request.

The old index stays available while embedding runs. Every new chunk must have
a complete usable vector in the same model space. The database's dimension
declaration is enforced when present; Mimir does not choose a dimension quota.
The complete replacement, removal of old evidence, recomputation of affected
beliefs and original loaded count share one transaction. Failure to save the
answer rolls back the replacement as well.

Deleting the project, explicitly cancelling the operation or replacing the
original index stops its owned embedding work. A stale preparation cannot
overwrite a newer document. Unfinished work explains the conflict and asks the
calling agent to discuss the original token with the user. It does not invent
a new token, silently recapture the file or cancel itself.

Completed results replay unchanged, including results from the exact older
document-loading plan. An unfinished older plan keeps its original steps and
answers and requires a user decision before separate corrected work starts.

The registered service entry point is `load_document_operation`. Public MCP
and CLI token routing is tracked separately in #85 and #86; the older direct
service entry point does not establish that routing guarantee.
