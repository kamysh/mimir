# Complete diagnostic fields

Failure and event constructors preserve the complete supplied tool name, event
kind and diagnostic detail. Line breaks and other characters remain in the
value; JSON escapes characters that need escaping. The recorded detail size is
the original UTF-8 byte length.

This removes the former 64-character tool-name cut, 48-character event-kind cut,
512-character failure-detail cut and 3,072-character event-detail cut. A repair
instruction at the end of a longer detail remains available in that value.

Trace-count, attempt-count, source-excerpt and file-size restrictions still
remain tracked in #108. This change makes no claim that later storage keeps
every diagnostic event. It adds no timeout, quota or dependency.
