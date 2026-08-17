# Claude Code setup — mimir

Hand this directory to Claude Code with the instruction:
**"Walk me through installing this. Show me each change before applying it and wait for my approval."**

Claude Code will read the reference files here, compare them against what is
already on the machine, propose the minimal diff for each step, and apply it
only after you confirm.

## Prerequisites (verify before starting)

- `~/.local/bin/mimir` and `~/.local/bin/mimir-mcp` installed (`mimir --version` works)
- `~/.config/mimir/config.toml` configured (`mimir stats` succeeds)
- `jq` on PATH
- Claude Code installed, `claude` on PATH

## What is in this directory

| File | Purpose |
|---|---|
| `skill/SKILL.md` | Target content for `~/.claude/skills/mimir/SKILL.md` |
| `CLAUDE.md` | Target content for the mimir section of `~/.claude/CLAUDE.md` |
| `settings.json` | Reference hooks — **not a drop-in replacement**, see Step 2 |

## Steps (each requires human approval before Claude Code acts)

### Step 1 — skill file

Claude Code should:
1. Read `skill/SKILL.md` and `~/.claude/skills/mimir/SKILL.md` (if it exists).
2. Show the diff.
3. Write the new file only after approval. Create `~/.claude/skills/mimir/` if absent.

### Step 2 — settings.json hooks

`settings.json` here is a **reference**, not a replacement. The existing
`~/.claude/settings.json` may have other permissions, hooks, and settings that
must be preserved.

Claude Code should:
1. Read `settings.json` and `~/.claude/settings.json`.
2. For each hook event, identify what is present in the reference but absent in the target.
3. Show the proposed additions as a clear before/after of the relevant sections.
4. Apply each addition only after approval. Never remove existing entries.

The hooks to add if absent:

- **`SessionStart`**: mimir skill reminder echo
- **`UserPromptSubmit`**: `mimir hook prompt` + per-prompt sentinel reset
- **`PostToolUse`** (matcher `mcp__mimir__query_relevant|mcp__mimir__query_document`): mimir sentinel creation
- **`PreToolUse`** (matcher `Edit|Write|Bash`): `mimir hook pretooluse`
- **`PreToolUse`** (matcher `Bash`): git/gh gate

See `settings.json` for the exact commands.

### Step 3 — CLAUDE.md (global instructions)

`~/.claude/CLAUDE.md` is loaded by Claude Code at the start of every session.
The `CLAUDE.md` here contains the mimir section only.

Claude Code should:
1. Read `CLAUDE.md` and `~/.claude/CLAUDE.md` (if it exists).
2. If the mimir section is already present, show what would change.
3. If absent, show the section that would be appended.
4. Apply only after approval. Never remove unrelated sections.

### Step 4 — register MCP server

Claude Code should run `claude mcp list` and check whether `mimir` is registered
and pointing at `~/.local/bin/mimir-mcp`.

If missing or wrong path:
```
claude mcp remove mimir --scope user   # only if it exists with wrong path
claude mcp add --scope user mimir ~/.local/bin/mimir-mcp
```

Show the proposed commands and wait for approval before running each one.

### Step 5 — verify

After all changes are applied:
1. Show the final `~/.claude/settings.json` for a last review.
2. Run `claude mcp list` to confirm `mimir` is registered and Connected.
3. Prompt the user to restart Claude Code for hooks and the new MCP binary to take effect.

## If muninn is also installed

When both mimir and muninn are wired, you can add a stronger enforcement hook
that requires both tools to be queried before any file access. This goes in
`PreToolUse` with matcher `Read|Edit|Write|Grep|Glob`:

```json
{
  "matcher": "Read|Edit|Write|Grep|Glob",
  "hooks": [{
    "type": "command",
    "command": "sid=$(jq -r .session_id 2>/dev/null); { [ -f \"/tmp/claude-mm-mimir-$sid\" ] && [ -f \"/tmp/claude-mm-muninn-$sid\" ]; } || { echo 'Policy: query mimir (mcp__mimir__query_relevant) AND muninn (mcp__muninn__search_*) BEFORE reading files or writing code. Run both, then retry.' >&2; exit 2; }"
  }]
}
```

Also add a `UserPromptSubmit` hook that resets the muninn sentinel each prompt:
```
sid=$(jq -r .session_id 2>/dev/null); rm -f "/tmp/claude-mm-mimir-$sid" "/tmp/claude-mm-muninn-$sid"
```

See `docs/claude-code-setup/settings.json` in the muninn repo for the full muninn hook set.

## Enforcing session project scoping (issue #9)

The SessionStart hook (above) only *reminds* the agent to run `mimir hook
set-project <name>` — a prose reminder alone gets skipped under load, the same
failure mode the `mimir hook stop` working-memory gate exists to prevent for
consolidation. To make it structurally enforced instead of just suggested, add
a second command to the same `Read|Edit|Write|Grep|Glob` `PreToolUse` matcher
used above: it allows the session's first file-touching tool call through
unconditionally (so the agent can look around enough to form a guess), then
blocks every call after that until `/tmp/mimir-session-project-$sid` exists —
the marker file `mimir hook set-project` writes.

```json
{
  "type": "command",
  "command": "sid=$(jq -r .session_id 2>/dev/null); pf=\"/tmp/mimir-session-project-$sid\"; ff=\"/tmp/claude-proj-seen-$sid\"; if [ -f \"$pf\" ] || [ ! -f \"$ff\" ]; then touch \"$ff\" 2>/dev/null; else echo 'Policy: this session has not declared a mimir project yet (issue #9), and this is not the first tool call — ask the user which project this session is about, or state a confident guess and let them correct it, then run: mimir hook set-project <name>. Retry after.' >&2; exit 2; fi"
}
```

Unlike the dual mimir/muninn marker above, `/tmp/claude-proj-seen-$sid` is
**not** reset on `UserPromptSubmit` — project scoping is a once-per-session
decision, not a once-per-turn one.
