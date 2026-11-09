# Complete log entries

Operational event formatting keeps the complete ordinary message text. The
existing removal of control characters still places an event on one line.
The tracing writer retains every byte it reports as accepted, across repeated
writes, explicit flushes and its final flush when dropped.

This removes the 8,192-character event cut and 32 KiB tracing-buffer cut. It
was followed by #226, which removes file-size clipping and rotation as well.
The entry-formatting test checks these paths independently of file retention.

The existing formal log protocol accepts the complete entry that reaches file
writing. No new formal module or buffer proof is required for these removals.
Its file model now requires complete append-only writes.

This addresses #225. No live logs or configuration are changed.
