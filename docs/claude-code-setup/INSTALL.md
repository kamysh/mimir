# Agent setup — Mimir for Codex and Claude Code

Mimir helps recover prior decisions, rejected approaches and lessons that would
otherwise be rediscovered. The skill explains how to query and evaluate that
knowledge and preserve useful findings. A startup reminder restores the purpose
of these tools at session start, resume and after context compaction.

Agree on the client(s), affected files and installation scope first. Compare
existing settings and back up affected files. Complete the approved stage without
asking again for every command. Preserve unrelated instructions, hooks, native
permissions and MCP servers. This guide changes agent integration, not database
configuration or services.

## Prerequisites

- Installed `mimir` and `mimir-mcp`, with the intended database reachable.
- The chosen client: Codex, Claude Code, or both.
- A POSIX shell for these examples; `jq` for configuration checks.
- For the combined reminder, Muninn's MCP server and skill also installed.

Reuse existing connection settings. Application/database installation is covered
by [README.md](../../README.md#installation) and [AGENTS.md](../../AGENTS.md).

## Register the MCP server

Inspect the selected client's existing `mcp list` / `mcp get mimir` output first.
For a new registration, using the default binary location:

```sh
# Codex
codex mcp add mimir -- "$HOME/.local/bin/mimir-mcp"
codex mcp get mimir

# Claude Code
claude mcp add --transport stdio --scope user mimir -- "$HOME/.local/bin/mimir-mcp"
claude mcp get mimir
```

Run only the chosen client's commands. An existing registration with the correct
path and scope needs no replacement. These start a local stdio process; registration
alone does not establish connectivity in an already-open session.
Sources: [Codex MCP](https://learn.chatgpt.com/docs/extend/mcp?surface=cli),
[Claude MCP](https://code.claude.com/docs/en/mcp).

## Install the shared skill and standing guidance

[skill/SKILL.md](skill/SKILL.md) is the canonical skill for both clients and the
repository's `install.sh`. It uses project-scoped queries, evidence evaluation and
selective durable writeback. No automatic retrieval or Stop gate is assumed.

| Client | Skill location for a new setup | Global instructions |
| --- | --- | --- |
| Codex | `~/.agents/skills/mimir/SKILL.md` | `~/.codex/AGENTS.md` or configured Codex home |
| Claude Code | `~/.claude/skills/mimir/SKILL.md` | `~/.claude/CLAUDE.md` |

Existing Codex installations may discover `~/.codex/skills`; update the actual
working skill location instead of creating duplicates. From the repository root,
for a new setup in the chosen client:

```sh
# Codex
mkdir -p "$HOME/.agents/skills/mimir"
cp docs/claude-code-setup/skill/SKILL.md "$HOME/.agents/skills/mimir/SKILL.md"
# Claude Code
mkdir -p "$HOME/.claude/skills/mimir"
cp docs/claude-code-setup/skill/SKILL.md "$HOME/.claude/skills/mimir/SKILL.md"
```

Merge [CLAUDE.md](CLAUDE.md)'s Mimir section into the client's global instructions;
its content applies to both clients. Replace an older Mimir section rather than
appending contradictory rules. Preserve other sections.
Sources: [Codex skills](https://learn.chatgpt.com/docs/build-skills),
[Claude skills](https://code.claude.com/docs/en/skills).

## Install one purpose-focused reminder

Choose [reminders/mimir.md](reminders/mimir.md) for Mimir alone, or
[reminders/mimir-muninn.md](reminders/mimir-muninn.md) when both tools and skills
are installed. The combined wording is shared with Muninn's installation guide.
If Muninn already installed a combined reminder, reuse that hook and its text
file; do not add another one for Mimir. Installing the second tool should update
an existing single-tool reminder to the combined version.

For a new reminder, from the repository root:

```sh
REMINDER_SOURCE=docs/claude-code-setup/reminders/mimir.md
# For both tools, select this instead:
# REMINDER_SOURCE=docs/claude-code-setup/reminders/mimir-muninn.md

# Codex
mkdir -p "${CODEX_HOME:-$HOME/.codex}"
cp "$REMINDER_SOURCE" "${CODEX_HOME:-$HOME/.codex}/mimir-reminder.md"
# Claude Code
mkdir -p "$HOME/.claude"
cp "$REMINDER_SOURCE" "$HOME/.claude/mimir-reminder.md"
```

Run only the selected client's copy commands. The reminder lives independently
of the source checkout. Adapt paths for a custom client configuration directory.

### Codex

Merge the `SessionStart` entry from [codex-hooks.json](codex-hooks.json) into
`${CODEX_HOME:-$HOME/.codex}/hooks.json`. Use one representation; do not duplicate
it in inline TOML or project hooks. Review and trust the new or changed definition
through `/hooks`; Codex skips untrusted definitions. Leave trust records to the
client. The unfiltered event covers startup, resume, clear and post-compaction
context. See the [Codex hook reference](https://learn.chatgpt.com/docs/hooks).

### Claude Code

Merge the `SessionStart` entry from [settings.json](settings.json) into
`~/.claude/settings.json`. Inspect it through `/hooks` and verify in a fresh
session. The unfiltered event includes startup, resume and compaction. See the
[Claude hook reference](https://code.claude.com/docs/en/hooks#sessionstart).

Both templates only read and print a text file. They perform no query or write,
require no ratings and impose no tool-call or consolidation gate. A deliberate
choice to omit the hook does not disable Mimir; report that setup choice.

## Upgrade an enforced setup

Changing the startup message alone leaves earlier enforcement active. Within the
agreed Mimir/Muninn integration scope, remove:

- Automatic `mimir hook prompt` and `mimir hook pretooluse` registrations.
- Query-sentinel reset/creation hooks and file-access gates that depend on them.
- Project-declaration marker gates/reminders used by that automatic injection.
- Required relevance ratings and per-turn writeback/consolidation Stop gates,
  including `mimir hook stop`.
- Older Mimir/Muninn reminders replaced by the single combined reminder.

Review the installed skill and global instructions too: remove fixed query/write
quotas, compulsory disposition lines and the instruction to make every insert
`working`. Durable findings use an explicit appropriate memory type; temporary
working beliefs need deliberate resolution when used. Existing beliefs are not
modified by this configuration update.

A personal Claude Stop critic that launches a second model is separate from
Mimir retrieval. When retiring that critic is part of the approved change, remove
its registration; retain its prompt/log files for recovery. Preserve Git guards,
collaboration hooks, memory-file loading and other unrelated behavior, including
any commands sharing a hook entry with the removed logic. Never replace the
entire settings file with this reference.

Legacy hook CLI commands remain available for explicitly chosen custom workflows;
the standard installer does not wire them. Optional scheduled belief-maintenance
judges are separate from the per-turn critic and are not installed, stopped or
reconfigured by this procedure.

## Verify configuration, delivery and usefulness separately

1. Parse the merged JSON; compare the diff with the backup. Confirm the selected
   reminder, skill and standing guidance agree and unrelated settings survived.
2. Run the actual reminder command directly. It should emit the selected text,
   exit zero and perform no retrieval or mutation. Example for a new Claude setup:

   ```sh
   printf '%s\n' '{"hook_event_name":"SessionStart","source":"compact"}' |
     sh -c 'cat "$HOME/.claude/mimir-reminder.md"'
   ```

   For Codex use the command from `codex-hooks.json`. Supplying `source: compact`
   manually tests the command's output, not client compaction.
3. Inspect client MCP registration and reconnect or use a fresh session. Make a
   focused `query_relevant` call for known stored knowledge and evaluate the result.
   A successful `mcp list` alone does not prove the running session is connected.
4. Confirm skill discovery and actual reminder delivery on startup, resume and
   after `/compact` in a disposable conversation. Use hook diagnostics/transcript
   evidence that the text reached model context. Report unsupported or untested
   events, including automatic compaction if only manual compaction was checked.
5. Give a fresh session an approach question with a relevant stored lesson,
   without explicitly naming the tool. Observe whether the agent retrieves and
   uses the lesson appropriately. If Muninn is present, also try a code-discovery
   question with the implementation location unspecified. Distinguish reminder
   delivery from useful tool selection; forced calls check connectivity only.

Report command checks, lifecycle delivery and behavioral observations separately.
Do not claim that parsing JSON or printing the reminder proves agent adoption.
