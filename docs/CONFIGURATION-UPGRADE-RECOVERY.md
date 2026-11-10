# Configuration upgrades and retries

An upgrade removes retired application limits and adds the required configuration
version. It preserves credentials, other settings and comments. An explicitly
supplied log directory replaces that setting; repeating the same request keeps
the chosen directory. Unsupported versions and invalid required settings leave
the selected file unchanged.

The intended result is defined by the existing pure document transformation in
`Mimir.ConfigurationUpgrade`. The recovery proof now establishes that every
successful result is a fixed point: reading that complete result and upgrading
again produces the same settings, preserved content and successful answer.

For example, if replacement succeeds but the process stops before reporting
success, the next invocation reads the complete upgraded file. It cannot remove
another setting or restore the retired limits. If preparation stops before
replacement, the original file remains available for the retry.

An unchanged retry still confirms the file and its containing directory on
disk. Matching bytes alone do not prove that a previous replacement finished
that confirmation. If either confirmation fails, the command reports the real
error and does not announce success; it keeps the selected bytes untouched.

The certificate follows the selected-file read, private preparation, complete
replacement and directory sync. Private preparation includes writing and syncing
the owned temporary file and checking that the selected original is unchanged.
It changes no public file. A failed filesystem step interrupts the operation;
it is not a completed upgrade. A completed retry reaches the original intended
file and answer after any shared interruption point, including replacement
whose acknowledgement was lost. Other application state is preserved as a
whole frame.

The certificate uses the existing `Mimir.AtomicFile.Storage` world, keeping both
the visible file and the confirmed durable mapping. Success establishes both.
Its power-loss lemma also covers either the old or the new complete file being
recovered before directory sync: either observation leads to the same completed
upgrade. It does not claim that unsynced data survives power loss or that it can
merge a simultaneous edit by an unrelated program. The native command rechecks
the original immediately before replacement and reports an observed conflict
instead of guessing how to merge it.

TOML parsing and preservation of comments remain standard library boundaries;
this work adds no parser or formatting proofs. The certificate is exported as
`ConfigurationUpgrade.Document.Replacement.recoverable`. Connecting the complete
CLI configuration lifecycle to mandatory certified dispatch remains unfinished
under #148 and the dispatcher work; this export alone does not enforce routing.
