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

The release runner also observes its disposable database's startup events.
Its owned entrypoint announces the final server start; bootstrap readiness
messages before that announcement do not count. The final server uses the C
message locale only inside this fixture, so its readiness event is stable.
The runner then requires a successful `pg_isready --timeout=0` probe. PostgreSQL
documents this flag as disabling the tool's default connection deadline; this
is an external command option, not a Mimir request convention. See the
[PostgreSQL command reference](https://www.postgresql.org/docs/current/app-pg-isready.html).

The runner stops and reaps only its log-reading process after readiness. Its
actual exit status and observed events are recorded separately, and output
from both streams is retained together. An intentionally stopped log reader
is therefore distinguishable from missing readiness or a failed final server.
Container cleanup still requires the original ownership label and identity.

The connection-guard listener waits for socket events. Its owner sends an
explicit stop event, the listener records any queued connection attempts, and
the owner joins the completed thread. No accept timeout or join allowance
decides whether the isolation check passed.

The Python cancellation helper also observes readiness directly. A blocked
standalone fake model writes its evidence and sends a local readiness event.
For a paused watcher, the helper reads the expected stderr message and checks
the already-written state evidence. Premature process exit, malformed events
and missing evidence are reported directly. The helper owns its listener,
stderr capture and process-wait tasks and finishes them before returning.
The fake model and its descendant block without a sleep duration.

The adapter fixture keeps MCP stdin open while awaiting the response to its
request. Closing stdin immediately after writing would cancel the request under
the server's existing disconnect behavior. Once the response with the expected
request ID arrives, the helper closes stdin, drains remaining output and awaits
the MCP process. It checks the selected configuration against the disposable
database contract and stores complete stdout, stderr and actual exit status.

`tests/judge-adapters.sh --cancellation-only` selects the stalled model,
descendant and paused-watcher checks through the maintained entrypoint. The
watcher check expects explicit retry rather than removed interval flags or an
invented backoff.

When the release runner is interrupted, it requests normal shutdown of its
owned command group and awaits the owner's actual exit. The cancellation helper
likewise sends SIGTERM to Mimir and waits for its existing stop handler to clean
up MCP and model work. Neither helper chooses a five- or ten-second allowance
or kills the outer owner because elapsed time passed. Output capture and owned
tasks finish before the helper returns. A controlled check verifies that an
owner reaps its child in a separate process group before that completion.
Other fixture restrictions remain tracked by #116.
