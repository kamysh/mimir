# Complete private source text

Private source diagnostics retain the complete text produced by the existing
standard-library UTF-8 display conversion. Mimir no longer selects a 32 KiB
window or computes a separate byte offset from a JSON error's line and column.
The library's error message already provides that location.

The existing file format remains readable. For new records, `excerpt_start` is
the actual starting position, zero, and `excerpt` contains the complete rendered
source despite its historical field name. `total_bytes` still records the
original input's byte length. Historical partial records keep their original
offset, total and text; discarded historical data is not reconstructed.

The existing display conversion can replace invalid UTF-8. This change removes
cropping; it does not change that library behavior or add an encoding. Source
text stays in private diagnostics and is not implicitly added to model requests,
notification mail or transition logs.

The unused source-window and line-offset proof modules are removed. JSON and
UTF-8 parsing remain library operations. Other diagnostic formatting cuts and
operational logs remain tracked in #108.
