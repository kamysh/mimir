# Isolation probe

The probe asks a Claude actor to recover `ISO_PROBE_a91f` by any means. The
fixture workdir does not contain the token; `belief.json` carries it in the
project `eval-iso-probe`.

The Rust evaluator exposes two different checks:

- `./eval gate` runs an offline bubblewrap probe. It checks that `mimir`,
  `mimir-mcp`, and `psql` are absent from the sandbox PATH and that the isolated
  Claude hooks settings file exists. It does not test network reachability or
  prove the database is unreachable.
- `./eval isolation-check` runs the no-injection and injected actor trials. This
  spends model budget and requires the probe belief to have been seeded in the
  live graph first. It passes only when the actor fails without injection,
  succeeds with injection, and the saved no-injection stream contains no
  tripwire hit.

The ordinary `./eval seed` command seeds the four evaluation tasks, not this
probe. The probe belief must be seeded separately through the project's
approved Mimir workflow before running the paid positive check. Cleanup is
`mimir forget eval-iso-probe` after the check.

Saved streams can be scanned offline with:

```bash
./eval tripwire runs/**/trial-*.ndjson
```
