# Operational log writes and batch startup

A successful log write preserves the current bytes and appends the complete
requested entry. Historical archives remain unchanged. There is no file-size,
archive-count or entry-size policy in the application log model.

The existing `OperationalLogRetention` module now describes this append-only
outcome. Its general laws state that the current contents gain the complete entry
and that all archives retain their contents. The obsolete rotation-step module
has been removed.

`OperationalLogProtocol` requires completed lock, append and descriptor-cleanup
observations. Its independent ownership policy proves that every file operation
occurs while the same lock is held. A success exposes the entire entry and exact
resulting contents. A failed append can leave only a prefix of that entry added
to the prior file, with the prefix length supplied by the filesystem receipt.
Lock failure does not claim an observed file state. These contracts do not prove
kernel behavior or crash durability.

`OperationalConfiguration` admits the chosen absolute log directory without
retention settings. Retired keys receive a diagnostic directing the caller to
`mimir config upgrade`. `ConfigurationUpgrade` accounts for every logging field:
only the retired keys disappear; every other field retains its value and order.
The same generic migration proof also serves the existing retired model settings.

`OperationalLifecycle` requires a checked log attempt for the configured
directory before a judge batch can proceed. The exact append result follows
from its successful receipt. A failed log attempt cannot authorize reviewing.
The actual `JudgeHostProtocol` consumes this receipt before state, database,
model or tool work in that batch. Its failure-stopping proof remains in force.

Native checks cover concurrent writes larger than the old file limit, exact
preservation of existing contents and archives, actionable retired-setting
diagnostics and an idempotent configuration upgrade. No production log or
configuration is changed by these checks.
