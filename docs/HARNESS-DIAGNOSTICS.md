# Failed harness diagnostics

When a judge model harness exits unsuccessfully, its subprocess boundary retains
all stderr and includes the complete explanation in its error. Stdout and stderr
are read concurrently. The error retains the original bytes even when they are
not valid UTF-8; its human-readable display uses replacement characters where
decoding requires them. Neither the old 64 KiB storage ceiling nor the old
512-character error excerpt applies.

This does not enlarge the judge's model request. Later saved-history and MCP
client diagnostic cuts remain tracked separately in #108.

The subprocess keeps its existing process-group ownership and cleanup. No
deadline, output quota or retry count is added. The existing Agda model preserves
every byte of either stream across each read, for arbitrary accumulated output
and incoming chunks.
