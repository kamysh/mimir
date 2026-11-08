# Complete diagnostic history

The judge retains every recorded attempt, including completed attempts, and
every selected experience ID and event. Events stay in their recorded order.
There is no event-count ceiling, selected-ID ceiling, per-trace byte ceiling or
attempt-retention count.

Finishing records the result and finish time without dropping events. Starting
a new attempt still marks abandoned running attempts as interrupted; it keeps
their other recorded evidence and all previous attempts. Private file ownership,
permissions, atomic replacement and fsync remain in place.

An old `events_omitted` value describes evidence already lost by an older
version. It remains intact. The current version neither adds omissions nor
pretends that the missing historical evidence has been recovered.

The lifecycle model keeps these preservation rules and requires a write
acknowledgement before reporting completion. The obsolete event-truncation,
trace-shrinking and attempt-pruning modules, and their unused list-pop helper,
have been removed. Source excerpts, other diagnostic formatting cuts and
operational logs remain tracked in #108.
