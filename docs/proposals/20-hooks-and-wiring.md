# Hooks & wiring — make retrieval automatic

The point of these hooks: **don't depend on Claude remembering to retrieve.**
Put relevant beliefs in front of it at deterministic points, and let the skill's
comply-or-override discipline do the rest.

Three hooks, each at a different cadence:

| Hook | Cadence | What it does | Injection mechanism |
|---|---|---|---|
| `SessionStart` | once / session | Reminds Claude the tools exist and to load the skill. | plain stdout (injected on exit 0) |
| `UserPromptSubmit` | once / turn | Runs `mimir query` on the prompt, injects matching beliefs. | plain stdout (injected on exit 0) |
| `PreToolUse` (Edit\|Write\|Bash) | every such tool call | Runs `mimir query` on the file path / command, injects matching beliefs **before the action runs**. | **JSON `additionalContext`** |

> **The one contract subtlety that bites people:** for `UserPromptSubmit` and
> `SessionStart`, plain stdout (exit 0) is added to Claude's context. For
> `PreToolUse`, **plain stdout is *not* injected** — you must emit JSON with
> `hookSpecificOutput.additionalContext`. The `PreToolUse` script below does
> exactly that. (`additionalContext` on `PreToolUse` requires a reasonably recent
> Claude Code; if `/hooks` shows it firing but nothing reaches context, update.)

All scripts **always exit 0** so a hook can never block or fail a tool call.
They no-op silently if `mimir`/`jq` are missing or there are no results.

---

## 1. Helper scripts

Create `~/.claude/hooks/` and drop in both scripts. They require `jq` (or swap
the parse for `python3 -c`).

### `~/.claude/hooks/mimir-pretooluse.sh`

```bash
#!/usr/bin/env bash
# PreToolUse hook for mimir. Reads the hook JSON on stdin, derives a query from
# the tool input, asks mimir for relevant beliefs, and injects them as
# additionalContext. NEVER blocks the tool: always exits 0.
set -uo pipefail
trap 'exit 0' EXIT

command -v mimir >/dev/null 2>&1 || exit 0
command -v jq    >/dev/null 2>&1 || exit 0

input="$(cat)"

# Edit/Write expose file_path/path; Bash exposes command. First non-empty wins.
query="$(printf '%s' "$input" | jq -r '
  .tool_input.file_path // .tool_input.path // .tool_input.command // empty
' 2>/dev/null | head -c 200)"

[ -n "${query:-}" ] || exit 0

results="$(mimir query "$query" --limit 3 2>/dev/null)"
[ -n "$results" ] || exit 0
case "$results" in "(no results)"*) exit 0 ;; esac

# PreToolUse plain stdout is NOT injected — additionalContext is.
jq -cn --arg ctx "mimir priors relevant to this action (treat as priors; comply-or-override per the mimir skill):
$results" '{
  hookSpecificOutput: {
    hookEventName: "PreToolUse",
    additionalContext: $ctx
  }
}'
```

### `~/.claude/hooks/mimir-prompt.sh`

```bash
#!/usr/bin/env bash
# UserPromptSubmit hook for mimir. Injects beliefs relevant to the prompt.
# Plain stdout IS injected for UserPromptSubmit, so we just print.
set -uo pipefail
trap 'exit 0' EXIT

command -v mimir >/dev/null 2>&1 || exit 0
command -v jq    >/dev/null 2>&1 || exit 0

input="$(cat)"
prompt="$(printf '%s' "$input" | jq -r '.prompt // empty' 2>/dev/null | head -c 500)"
[ -n "${prompt:-}" ] || exit 0

results="$(mimir query "$prompt" --limit 5 2>/dev/null)"
[ -n "$results" ] || exit 0
case "$results" in "(no results)"*) exit 0 ;; esac

printf '[mimir priors — treat as priors, comply-or-override per the mimir skill]\n%s\n' "$results"
```

Make them executable:

```bash
chmod +x ~/.claude/hooks/mimir-pretooluse.sh ~/.claude/hooks/mimir-prompt.sh
```

---

## 2. `settings.json` block

Merge this into `~/.claude/settings.json` under the top-level `"hooks"` key.
**Do not overwrite the file** — append to existing arrays. Multiple hooks per
event are allowed and run in parallel, which is why the muninn reminder can sit
alongside the mimir query.

```json
{
  "hooks": {
    "SessionStart": [
      {
        "hooks": [
          {
            "type": "command",
            "command": "echo 'mcp__mimir tools are available. Invoke the mimir skill now: load the read+write belief-graph protocol (consult before >2-step exploration, errors, or approach choices; write back what recurs).'"
          }
        ]
      }
    ],
    "UserPromptSubmit": [
      {
        "hooks": [
          { "type": "command", "command": "\"$HOME/.claude/hooks/mimir-prompt.sh\"" }
        ]
      },
      {
        "hooks": [
          { "type": "command", "command": "echo 'Also query muninn for relevant code knowledge (mcp__muninn__search_hybrid) before reading files — muninn = where code is, mimir = what you learned.'" }
        ]
      }
    ],
    "PreToolUse": [
      {
        "matcher": "Edit|Write|Bash",
        "hooks": [
          { "type": "command", "command": "\"$HOME/.claude/hooks/mimir-pretooluse.sh\"" }
        ]
      }
    ]
  }
}
```

Restart Claude Code for the hooks to take effect.

---

## 3. Verify

```bash
# Scripts parse stdin JSON and emit the right shape:
echo '{"prompt":"flake.nix onnxruntime ABI"}' | ~/.claude/hooks/mimir-prompt.sh
echo '{"tool_name":"Edit","tool_input":{"file_path":"flake.nix"}}' | ~/.claude/hooks/mimir-pretooluse.sh   # → JSON with hookSpecificOutput

# Config is registered (interactive):
#   /hooks      → shows SessionStart, UserPromptSubmit, PreToolUse entries
```

The `mimir-pretooluse.sh` check should print a JSON object containing
`additionalContext`; `mimir-prompt.sh` should print belief lines or nothing.
Both should print nothing (and exit 0) if the graph has no match.

---

## 4. Tuning — the cost you just took on

`PreToolUse` on `Edit|Write|Bash` adds one `mimir query` (a DB round-trip) before
*every* such tool call. That is the deliberate trade — re-derivation cost for
hook latency — but tighten it if it drags:

- **Narrow the matcher.** Drop `Bash`, or gate the Bash branch in the script to
  only query when the command looks exploratory/expensive (matches
  `cargo|nix|test|build|docker`), skipping `ls`/`cat`/`echo`.
- **Raise the bar.** `--limit 2`, and consider suppressing injection unless the
  top hit clears a probability floor (add `awk -F'p=' '...'` to filter the
  `mimir query` lines on `p≥0.6`). High-probability priors are the ones worth
  interrupting for.
- **Disable fast.** Remove the `PreToolUse` block (or `chmod -x` the script — it
  no-ops) and keep just `UserPromptSubmit` if per-tool injection is too chatty.

---

## 5. Optional CLI enhancement (hand to Claude Code)

The hooks currently consume `mimir query`'s human format, whose `content` is
truncated to 70 chars (`crates/cli/src/main.rs::cmd_query`, the `trunc(&b.content, 70)`
call). That's fine for recognition but thin for injected context. Small, isolated
improvement: add a `--format json` flag to the `Query` subcommand that prints one
JSON object per belief with **full** `content`, `id`, `probability`, `confidence`,
`project`. Then change both scripts to call `mimir query "$q" --limit N --format json`
and format the injected block from full content. Acceptance: `mimir query foo
--format json` emits valid JSONL; the human format is unchanged when the flag is
absent. This pairs naturally with Phase 1 but is independent of it.
