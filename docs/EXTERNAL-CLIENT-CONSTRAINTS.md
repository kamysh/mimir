# External startup-reminder constraints

Checked against official documentation on 2026-11-07 for #112 and #172.

Mimir's source templates omit the former five-second command timeout. The
reminder only prints an installed static guidance file; it does not run a
review or contact a model.

Omission does not establish unlimited execution. The official
[Codex hook documentation](https://learn.chatgpt.com/docs/hooks) specifies a
600-second default for ordinary command hooks. The official
[Claude Code hook reference](https://code.claude.com/docs/en/hooks) likewise
specifies that default for a synchronous SessionStart command hook.

On 2026-11-07 the user approved this as an external constraint for the static
startup reminder only. It does not authorize a Mimir database, embedding or
review deadline, and no installed settings were changed.
The reviewed documentation did not establish an unbounded synchronous mode.
Changing execution to a background hook changes when guidance can arrive and
must not be an automatic workaround. Nor should an agent invent a large
timeout or assume an undocumented zero disables it.

This decision is recorded under
[#112](https://github.com/kamysh/mimir/issues/112), whose wider audit remains
open. A successful template parse
or local invocation of `cat` does not verify delivery by an installed client.
Verify actual startup delivery through that client's diagnostics, and report
a client timeout separately from Mimir application behavior. These source
changes do not update installed settings or claim that their deadlines changed.
