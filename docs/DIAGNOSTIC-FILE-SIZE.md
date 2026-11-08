# Complete private diagnostic files

Judge state files have no application byte ceiling. This includes
`judge-diagnostics.json`, whose former 3 MiB ceiling has been removed. The native
helpers no longer carry an unused optional size limit.

The same file protections still apply: owned private directories, owner-only
files, no symlink following, exclusive temporary creation, atomic replacement
and fsync. An oversized-looking file is not a permission violation; unsafe
ownership or permissions still prevent reading it.

The existing persistence model selects no size ceiling for any state-file name.
The remaining trace-count, attempt-count, per-trace and source-excerpt cuts are
separate work in #108. This change is the file-storage prerequisite for keeping
that additional evidence.
