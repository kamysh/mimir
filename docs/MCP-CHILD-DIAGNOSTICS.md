# MCP child diagnostics

The judge owns its MCP child and stderr reader. If the response stream ends,
the client stops the child's process group, reaps the child and joins that
reader before returning diagnostic evidence. It no longer sleeps for 20 ms or
guesses whether the reader has caught up.

The returned error retains every captured stderr byte, including invalid UTF-8,
and reports cleanup or read problems alongside it. Its display includes the
complete decoded explanation. The old 4 KiB tail and 512-character excerpt are
removed. Dropping the client also aborts its owned reader task.

This adds no deadline, output quota or retry count. Saved diagnostic history and
operational logs still have separate work tracked in #108. An ended response
stream does not prove whether an earlier business operation committed; callers
must use the operation's outcome readback rather than infer success or rollback.

The existing framing model now waits for cleanup and reader completion. Its
general joined-diagnostic theorem preserves the captured bytes and all cleanup
and read issues. UTF-8 display remains a standard-library dependency.
