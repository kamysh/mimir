# Complete log entries

Operational event formatting keeps the complete ordinary message text. The
existing removal of control characters still places an event on one line.
The tracing writer retains every byte it reports as accepted, across repeated
writes, explicit flushes and its final flush when dropped.

This removes the 8,192-character event cut and 32 KiB tracing-buffer cut. It
does not yet remove file-size clipping or rotation; those remain in #109.
The focused test uses entries below the existing file-size limit to check these
two formatting paths independently of the remaining retention policy.

The existing formal log protocol accepts the complete entry that reaches file
writing. No new formal module or buffer proof is required for these removals.
Its file-retention model will change with the retention fix.

This addresses #225. No live logs or configuration are changed.
