# Process readiness and cancellation checks

The real CLI cancellation check starts a private loopback listener before the
CLI. Its fake MCP server and model connect only after their owned descendants
have started, and report their process IDs. The check sends SIGINT or SIGTERM
only after both owners report readiness. It covers both `judge run` and
`judge watch`.

The watcher subscribes to PostgreSQL before starting MCP. This check requires
the maintained disposable database fixture and validates its settings before
starting the CLI. It never guesses a localhost deployment address or loads the
installed configuration. The fake MCP/model processes do not write business
records in the fixture.

Each owner and its descendant keep the event connection open. The descendants
wait on private FIFOs, without a sleep duration. After stopping the CLI, the
check waits for the CLI's actual exit and for EOF on both event connections,
then checks that the reported processes have stopped. A premature CLI exit is
reported while waiting for readiness. Readiness is not inferred from a file
appearing or from elapsed time.

The MCP argument checks similarly collect complete process output and await
the actual exit. They retain the missing-configuration, malformed-configuration
and no-database-connection assertions. They have no startup polling interval or
five-second deadline.

These checks introduce no test watchdog. A stuck operation remains visible as
a running check until it is explicitly stopped. This is a test-fixture change,
not a production waiting policy. Other fixture waits remain tracked by #116.
