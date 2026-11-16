# Public changes and submitted software-list requests

Checked on 2026-10-20 using the GitHub account `kamysh`.

## Published and checked

All three projects now have the approved description, search topics, README
introduction, links to the other projects, and a complete explanatory article.
The public files were fetched from GitHub after publication and compared with
the local text. Descriptions and search topics were also read back and checked.

| Project | Public project page | Public article | Published commit |
| --- | --- | --- | --- |
| Kryzhen | [kamysh/kryzhen](https://github.com/kamysh/kryzhen) | [PostgreSQL migrations with dependencies and multiple schemas](https://github.com/kamysh/kryzhen/blob/main/docs/articles/dependency-based-migrations.md) | `64cdea34c5be31702741cc927a935049e3ba720d` |
| Muninn | [kamysh/muninn](https://github.com/kamysh/muninn) | [Code search across Git worktrees](https://github.com/kamysh/muninn/blob/main/docs/articles/worktree-code-search.md) | `52a43627f383259310f7a9eaf6bb85e4e491582b` |
| Mimir | [kamysh/mimir](https://github.com/kamysh/mimir) | [Reasoning memory with evidence and corrections](https://github.com/kamysh/mimir/blob/main/docs/articles/reasoning-memory.md) | `10c601357ce7f9866f3b9754ca24cd4862f1abaa` |

The articles identify the AI writer. No software release was created, no
program behavior was changed, and no system setting was changed. This establishes
public availability of the material, not increased readership or adoption.

## Glama completed; both software-list requests submitted

Both projects were submitted to Glama, approved, and verified publicly.
GitHub sign-in as the repository owner unlocked both admin pages.

The current Glama admin interface generates a Dockerfile from build and startup
commands. Both configurations were adapted to that form, built locally, and
tested with two client sessions and real database reads. The saved Glama settings
match the tested configuration. Both remote test jobs succeeded, both public
badges show A, and an unauthenticated author search returned both projects.
See [the complete test report](glama/README.md).

| Project | Public Glama page | Remote test |
| --- | --- | --- |
| Muninn | [Muninn](https://glama.ai/mcp/servers/kamysh/muninn) | success, 1m 16.6s |
| Mimir | [Mimir](https://glama.ai/mcp/servers/kamysh/mimir) | success, 1m 33.3s |

No Glama release or new GitHub software release was created.

The software-list entries now include the verified badges. Each dedicated
working copy contains one committed README addition, with no unrelated changes:

- Muninn: 3a54023ca3a33c851c79d53dc5d30cf3195367ee
- Mimir: 85dd4b0307eb2b933bdeeb8bd7487438fbfbe9f4

The [GitHub fork](https://github.com/kamysh/awesome-mcp-servers) was created and
its upstream was verified. A final duplicate search found no existing request
for either repository.

The initial branch push was blocked because this external checkout had no
registered publication checks. After explicit approval, the
[two-check registration](publication-checks.proposed.json) was added to
`/home/kamysh/.codex/hooks/publication/verification-policy.json`. All other
entries and the file mode were preserved. The official verification runner
passed both checks for both exact commits: no whitespace errors and no changes
outside README.md. Both branches were then pushed without force.

| Project | Submitted request | Verified result |
| --- | --- | --- |
| Muninn | [Add Muninn to Developer Tools, #17148](https://github.com/punkpeye/awesome-mcp-servers/pull/17148) | Open; one README insertion, no deletions |
| Mimir | [Add Mimir to Knowledge and Memory, #17149](https://github.com/punkpeye/awesome-mcp-servers/pull/17149) | Open; one README insertion, no deletions |

The published titles, bodies and entry text match the reviewed files. Both
requests have `has-glama`, `has-emoji` and `valid-name` labels. Neither has an
assignee or a requested reviewer. GitHub's `check-submission` check succeeded
for both requests; the optional `welcome` job was skipped. The list maintainers have not yet accepted
either request; submission does not establish an accepted entry.

## Local work preserved

The separate working copies used for the three successful publications were
clean and have been removed. Their commits remain in the public repositories.
The original working files were not updated or reset. Kryzhen's existing
`flake.lock` modification and untracked `z` were preserved; Muninn's original
checkout remains clean. Mimir retains the local `docs/public-visibility/` drafts.
The two software-list working copies were also removed after their clean state
and published requests were verified. Their local branches and the fork branches
remain available.

## Receipts

Complete logs and read-back results are retained under
`/tmp/publicity-publish.0rmn6T/`:

- `kryzhen-publication-receipt.json`, `muninn-publication-receipt.json`,
  `mimir-publication-receipt.json`
- `kryzhen-publication.log`, `muninn-publication.log`, `mimir-publication.log`
- `duplicate-check.log`, `prepare-list.log`, `glama-lookup.log`
- `*-glama-badge.body`, which preserve the missing-listing images
- `cleanup-published.log`

The exact public README and article bytes, request responses and exit statuses
are retained alongside those logs. No account tokens are included in this report.

Complete Glama build, protocol-test, successful submission and page-check records
are retained under `/tmp/publicity-glama.KCf7M0/`; see
[the test and submission report](glama/README.md). The task browser connection
was closed after verification. Personal Chrome settings and installed MCP
settings were not changed.

The final policy backup, official verification receipts, push logs, GitHub
responses, exact-text comparisons and cleanup receipts are retained under
`/tmp/publication-finish.vqs4vbbh/`. In particular,
`muninn-publication-receipt.json` and `mimir-publication-receipt.json` record the
verified requests. The approved publication-policy addition is the only
installed configuration change in this final step.

The final local document check passed: 44 internal prose links resolve, JSON
files parse, and code fences are balanced. Links inside copied README examples
remain relative to their intended project destinations. The publication-hook
outcome was recorded in Mimir as experience
`964e7041-512c-485c-8aee-5b664037c8e2`, revision 1.

## mcp.so requests submitted

On 2026-10-22, both listing packages were submitted to mcp.so's official GitHub
queue: [Muninn #5968](https://github.com/chatmcp/mcpso/issues/5968) and
[Mimir #5969](https://github.com/chatmcp/mcpso/issues/5969). Their public titles
and bodies were read back and matched the prepared files. Both requests are
open, posted as `kamysh`, without assigned people.

The website's form shows a $39 fee per server. The open GitHub submission route
was used instead, without payment. Submission does not establish acceptance or
publication on mcp.so. [Package and verification](mcp-so/README.md).

## Nix project changes published; search request submitted

The [Nix publication report](nix/README.md) records the three merged project
changes and [Nix search request #1602](https://github.com/NixOS/nixos-search/pull/1602),
which is open for review. All three normal packages
built on x86_64 Linux, and all six executables passed version and help startup
checks. Mimir needed a separately approved Linux build repair: its normal Nix
package lacked `pkg-config` and OpenSSL. The repaired candidate passed its build
and startup checks.

The descriptions and license metadata passed evaluation on the four advertised
systems and Nix search's own package extraction. Static and other-platform
compilation and database-backed runtime tests were not performed in this stage.
The public README and package files matched the reviewed changes byte for byte.
The search extractor also passed against the three public merge commits. The
external request's exact text and three added sources were verified; its
reported check passed. Acceptance and appearance in search remain pending.

The four approved publication-check registrations were applied, preserving
unrelated settings. Official commit checks passed. All four clean task
worktrees were removed; branches remain. No installed profile, application
settings, services or system configuration changed.
