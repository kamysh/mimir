# Time already represented by belief counts

Each belief stores `decay_accounted_at`: the time already represented by its
current evidence counts. This is separate from `last_activated_at`. Decay charges
only the interval after the later of these two times.

For example, counts of 100 and 10 with daily retention 0.5 become 50.5 and 5.5
after one day. Running another operation at that same time keeps 50.5 and 5.5.
After another full day they become 25.75 and 3.25. The earlier implementation
charged the full age since activation again on every call.

A registered operation uses its original PostgreSQL reservation time, factor
and project on every retry. Its changed counts, accounted times and both
original answers commit together. A saved retry returns the original answer.
If the operation was reserved before a later posterior write, it cannot move
that write's baseline backward or charge an interval those counts already
represent.

Every posterior publication records the time represented by its new counts.
This includes propagation, source/review changes, evidence changes and deletion
of a related belief. Ordinary writers sample PostgreSQL time after acquiring
the shared write lock. Registered writers use their original reservation time.
The stored baseline can only move forward. Activation remains a separate event.
Source and review history retain their existing transaction timestamps; those
recorded times and the separate posterior clock reading remain distinct.

Decay uses the full elapsed nanoseconds, so advancing the baseline does not
discard a fractional second. An unchanged or earlier clock returns the exact
stored counts before calculating a power. Every changed representable count
is retained; there is no epsilon allowance that hides small changes.

All selected fact beliefs advance their accounting baseline, including a fact
whose counts stay unchanged. The `decayed` reply counts numerical changes.
Experiential and working beliefs, other projects and unrelated stored data are
preserved.

The source migration initializes missing baselines at one PostgreSQL time and
preserves all existing counts, original priors, probabilities and existing
baselines. Earlier history cannot establish how much decay the current counts
already include. The upgrade therefore begins new accounting at that time
without recalculating old counts. This change does not itself run a migration
against an installed database.

`DecayRecovery` defines the complete desired stored state and requires a
recovery proof before its registered operation can be assembled. Its
`sameTimeCannotChargeAgain` theorem covers different operation tokens at the
same accounted time. Isolated database checks cover that case, lost replies,
rollback of counts and timestamps, migration preservation and interaction with
posterior writes. Public token and dispatcher integration remain their existing
follow-up issues.
