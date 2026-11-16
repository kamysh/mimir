# Directory entries and submission copy

The two MCP entries and PR bodies below have been submitted. The conditional
Kryzhen entry remains a draft. Duplicate checks preceded the two submissions.

Publication update, 2026-10-20: the list's automated checks additionally ask for a
Glama listing, passed checks and a score badge. Both project pages have now been
approved and verified publicly. Ownership access and remote tests succeeded;
both public badges show A. The approved local README checks passed, and both
requests are public and open:
[Muninn #17148](https://github.com/punkpeye/awesome-mcp-servers/pull/17148) and
[Mimir #17149](https://github.com/punkpeye/awesome-mcp-servers/pull/17149).
Their text and labels were read back and checked; see
[the results](publication-results.md).

## Muninn in Awesome MCP Servers

Destination: [punkpeye/awesome-mcp-servers](https://github.com/punkpeye/awesome-mcp-servers).
File: `README.md`. Section: `Developer Tools`, anchor `developer-tools`.
Follow the contribution guide's alphabetical insertion rule; do not reorder
unrelated entries to repair the list's existing ordering.

Exact entry:

```markdown
- [kamysh/muninn](https://github.com/kamysh/muninn) 🦀 🏠 🍎 🐧 - Code search for AI coding agents with hybrid retrieval, structural search and shared indexing across Git worktrees. Requires PostgreSQL with pgvector and Apache AGE. [![kamysh/muninn MCP server](https://glama.ai/mcp/servers/kamysh/muninn/badges/score.svg)](https://glama.ai/mcp/servers/kamysh/muninn)
```

PR title:

```text
Add Muninn to Developer Tools
```

PR body:

```markdown
Adds [Muninn](https://github.com/kamysh/muninn), a Rust MCP server for code search,
under Developer Tools.

Muninn supports semantic, full-text, hybrid and structural search. Linked Git
worktrees share unchanged indexed content while searches select a particular
checkout. The repository includes installation instructions for Linux and macOS
and documents its PostgreSQL prerequisites.

I maintain the project. This submission was prepared with AI assistance.
```

## Mimir in Awesome MCP Servers

Destination: the same repository. File: `README.md`. Section: `Knowledge & Memory`,
anchor `knowledge--memory`. Submit as a separate PR so each project can be
reviewed independently.

Exact entry:

```markdown
- [kamysh/mimir](https://github.com/kamysh/mimir) 🦀 🏠 🍎 🐧 - Persistent reasoning memory for AI coding agents, with evidence provenance, typed belief relationships and a revisioned experience ledger. Uses PostgreSQL and Apache AGE. [![kamysh/mimir MCP server](https://glama.ai/mcp/servers/kamysh/mimir/badges/score.svg)](https://glama.ai/mcp/servers/kamysh/mimir)
```

PR title:

```text
Add Mimir to Knowledge and Memory
```

PR body:

```markdown
Adds [Mimir](https://github.com/kamysh/mimir), a Rust MCP server for persistent
reasoning memory, under Knowledge & Memory.

Mimir preserves decisions, rejected approaches and evidence across agent
sessions. Its experience ledger retains incident and review history, rejects
stale revisions, and supports correcting a review's contribution to the belief
graph. The repository documents setup, data flow and the optional review runner.

I maintain the project. This submission was prepared with AI assistance.
```

Both entries use the list's Rust/local/macOS/Linux markers. The local marker
describes the server deployment option; it does not claim that hosted embeddings
or a cloud agent keep source and memory on the machine. Neither entry claims
Windows support.

## Kryzhen in Awesome Postgres

Conditional destination:
[dhamaniasad/awesome-postgres](https://github.com/dhamaniasad/awesome-postgres).
File: `README.md`. Section: `Utilities`.

This is not in the immediate submission queue. The
[contribution rules](https://github.com/dhamaniasad/awesome-postgres/blob/master/CONTRIBUTING.md)
require recognition/adoption and production-use maturity. Existing source use
in Muninn and Mimir establishes integration, not those external qualifications.
Do not invent adoption or ask the maintainer to recruit users to qualify.

Prepared entry, if eligibility can later be established:

```markdown
* [Kryzhen](https://github.com/kamysh/kryzhen) - dependency-based PostgreSQL migrations with a Rust library and CLI, forward-only SQL and independent per-schema tracking.
```

PR title:

```text
Add Kryzhen to Utilities
```

PR body, usable only after the eligibility check succeeds:

```markdown
Adds [Kryzhen](https://github.com/kamysh/kryzhen) under Utilities.

Kryzhen is a Rust library and CLI for forward-only PostgreSQL migrations with
named dependencies. The same migration set can be applied independently to
multiple schemas. It uses mallard's migration format and tracking table.

I maintain the project. This submission was prepared with AI assistance.
```

## Editorial destinations excluded from this package

This Week in Rust's current
[submission rules](https://github.com/rust-lang/this-week-in-rust#llm-written-articles)
exclude LLM-written articles. Its Project/Tooling Updates section also no longer
accepts PR submissions. Do not submit these article drafts there, disguise their
authorship, or recast them as a tooling PR to bypass the rule.

The official MCP reference-servers repository is not being treated as a general
third-party directory. PulseMCP form URLs could not be verified in this research;
they are not represented as ready submission destinations.

## Source rules

- [Awesome MCP Servers contribution guide](https://github.com/punkpeye/awesome-mcp-servers/blob/main/CONTRIBUTING.md)
- [Awesome MCP Servers categories and markers](https://github.com/punkpeye/awesome-mcp-servers#server-implementations)
- [Awesome Postgres contribution guide](https://github.com/dhamaniasad/awesome-postgres/blob/master/CONTRIBUTING.md)
- [This Week in Rust submission rules](https://github.com/rust-lang/this-week-in-rust#readme)
