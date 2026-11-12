# External guarantees

Mimir treats UUIDs as abstract identities that can be compared for equality.
PostgreSQL supplies database record UUIDs; the specification does not implement
UUID generation or rely on their ordering.

A committed transaction succeeds and its client receives its result. An
unsuccessful transaction leaves its proposed changes uncommitted. The recovery
contract uses these assumptions rather than modeling a lost successful result.

Library operations and operating-system mechanisms are external. The
specification states the application behavior that depends on them without
implementing their internal formats or algorithms.
