# Consistent CLI observations

The CLI's statistics, contradiction details and intervention details use one
read-only database view for each complete answer. If another client deletes a
belief while an answer is being collected, that answer retains its original
counts and displayed text; the next command sees the deletion.

Statistics reuses the existing graph counts. Contradiction and intervention
displays use belief records returned with the pair selection or calculation,
rather than looking up their text afterward. The existing terminal layout,
directed-edge counts, contradiction deduplication and numerical behavior stay
unchanged. Numerical overlays used for an intervention are temporary; returned
belief details are the physical records from the original view.

`StorageReadBinding.BasicReads` includes the statistics certificate.
`CLI.DatabaseObservations` derives these three complete answers from the stored
world and the existing checked intervention calculation. The binding retains an
actual committed-read event and uses its snapshot for that certificate. A
completed display emits exactly the selected output lines without further
database requests; formatting remains the existing terminal-library boundary.

The operation inventory at commit
`441720f4e4dac0d599471a139603ec3ff5fde829` classifies all 30 CLI leaves. Its read
paths are accounted for as follows; this change completes only the three
database observations above.

| Paths | Meaning to reuse and remaining work |
| --- | --- |
| stats; list; patterns; query; contradictions; intervene; evidence list; doc query | Existing graph counts, belief/pattern/evidence reads, full retrieval result, checked intervention and document-query meanings. List ordering and requested selection remain the existing pure CLI projection. Mandatory dispatcher wiring remains #74/#76. |
| hook prompt; hook pretooluse; hook stop | Full retrieval and its availability report for prompt/pretool, scoped Working-belief selection for Stop. No hook is installed or enabled. Dispatcher wiring remains #74/#76. |
| config check; judge check-config; judge status; judge diagnostics; judge diagnose | Existing configuration validation, state-read receipts, historical snapshot/trace selection and public diagnostic projection. Their actual selected file observations still need to be tied to their printed result. This work remains unfinished. |
| help; version; parser correction | Additional effect-free entry paths, rather than CLI leaves. Their output contract remains unfinished. |
| hook set-project | A session-file write, not a read-only command. Its file-write result cannot be inferred from its database read or exit code. |

The remaining write leaves belong to their corresponding existing work:
initialization/configuration upgrade, project deletion, decay, sweeping,
reembedding, evidence addition, belief/pattern deletion, document loading and
clearing, and judge run/watch. Initialization/configuration writes belong to
#148's file-state work. No database-read certificate is used to claim those
writes are safe.

This is a partial implementation of #149. It introduces no new file model,
formatter proof, hook installation, public tool, quota or timeout.
