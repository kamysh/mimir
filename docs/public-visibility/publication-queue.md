# Where to publish and what each step needs

The assistant does the work below after approval for the relevant step. The
maintainer does not need to find users, write articles or build an audience
first. The GitHub descriptions and articles are now public. Both projects passed
Glama's checks and appear in its public search. The approved local publication
checks also passed, and both software-list requests have been submitted:
[Muninn #17148](https://github.com/punkpeye/awesome-mcp-servers/pull/17148) and
[Mimir #17149](https://github.com/punkpeye/awesome-mcp-servers/pull/17149).
They remain open for the list maintainers' decision.
See [the publication results](publication-results.md) and
[the test and submission report](glama/README.md).

## Steps that can use the existing projects

| Order | Action | Where | Material already written | What is needed before acting |
| --- | --- | --- | --- | --- |
| 1 | Improve the three project pages | `kamysh/kryzhen`, `kamysh/muninn`, `kamysh/mimir` on GitHub | [Descriptions and introductions](repository-copy.md) | Approval to change those public pages; working GitHub access |
| 2 | Publish one explanatory article in each project | The three GitHub repositories | [Kryzhen](articles/kryzhen.md), [Muninn](articles/muninn.md), [Mimir](articles/mimir.md) | Approval to add the files publicly; working GitHub access |
| 3 | Add Muninn to a list of coding tools | [Awesome MCP Servers, Developer Tools](https://github.com/punkpeye/awesome-mcp-servers#developer-tools) | [Exact entry and submission text](directory-submissions.md#muninn-in-awesome-mcp-servers) | Submitted as #17148; checked text, labels and README-only change; awaiting the maintainer decision |
| 4 | Add Mimir to a list of memory tools | [Awesome MCP Servers, Knowledge and Memory](https://github.com/punkpeye/awesome-mcp-servers#knowledge--memory) | [Exact entry and submission text](directory-submissions.md#mimir-in-awesome-mcp-servers) | Submitted separately as #17149 with the same checks; awaiting the maintainer decision |
| 5 | Introduce the three projects on the author's profile | `kamysh/kamysh` on GitHub | [Profile introduction](repository-copy.md#github-profile-introduction) | Inspect any existing profile text, then obtain approval to merge this introduction |

No new software release is needed for these steps. The software-list maintainers
decide whether to accept the entries. A submitted request and an accepted entry
will be reported separately.

### Exact article destinations

Copy each complete article into its own project, preserving the disclosure about
AI authorship:

| Project | File to add | Article title |
| --- | --- | --- |
| Kryzhen | `docs/articles/dependency-based-migrations.md` | Kryzhen PostgreSQL migrations with dependencies and multiple schemas |
| Muninn | `docs/articles/worktree-code-search.md` | Muninn code search across Git worktrees |
| Mimir | `docs/articles/reasoning-memory.md` | Mimir reasoning memory with evidence and corrections |

Link the article from that project's README after the introduction. GitHub then
provides a public address for the complete article without a new publishing
account or website. Publishing does not guarantee that a search engine will
include the page or give it a particular position.

If publication uses pull requests, the assistant prepares the changes in
separate working copies, leaves unrelated changes alone, and follows the
applicable GitHub publication instructions. Preparation itself made no public
changes; the subsequently approved commits and pushes are recorded in
[the publication results](publication-results.md). The software-list requests
are now public and open for review.

## Muninn and Mimir on mcp.so

Prepared packages and submitted [Muninn #5968](https://github.com/chatmcp/mcpso/issues/5968)
and [Mimir #5969](https://github.com/chatmcp/mcpso/issues/5969) through the
official GitHub queue on 2026-10-22. Exact public titles and bodies verified.
No payment was made. Website acceptance and appearance remain unverified;
there is no confirmed review date. [Files and results](mcp-so/README.md).

## All three projects in Nix search

The [Nix publication and verification](nix/README.md) are complete. All three
normal Linux packages built, including the separately approved Mimir build
repair. All six programs passed version and help startup checks. The proposed
descriptions and licenses pass the search website's package extractor.

The three project patches are merged publicly, their exact public files and
package information verified, and [Nix search request #1602](https://github.com/NixOS/nixos-search/pull/1602)
is open. Its exact text and three-source change were read back successfully.
It has no assigned people, review requests or labels, as approved. Its reported
check passed. Acceptance and appearance in the Flakes search remain pending.
The scoped publication checks were registered and passed. Clean task worktrees
were removed. No installed profile or system configuration changed.

## Kryzhen on crates.io and docs.rs

These services let Rust developers find a library, read its API documentation
and install it through their usual tools.

The proposed public package names are `kryzhen` for the library and `kryzhen-cli`
for the command-line program. The executable remains `kryzhen`. The inspected
source is version `2.0.3`; this does not establish that those names or that
version are available on crates.io.

The assistant can do the following in a separately approved preparation step:

1. Check whether the names are available or already owned by this account.
2. Add the descriptions, repository links, README references and search terms
   below to the two package descriptions in the source files.
3. Add a registry version alongside the CLI's existing local library dependency:
   `kryzhen = { path = "../kryzhen", version = "2.0.3" }`, if `2.0.3` remains the
   approved publication version. The current path-only dependency cannot be
   published to crates.io as it stands.
4. Prepare the downloadable source packages, inspect their contents, and run the
   build checks without uploading them.
5. Present the exact files and check results for publication approval. After
   approval, publish the library before the CLI and verify both public pages.
6. Check whether docs.rs builds the library documentation successfully. Report a
   failed documentation build separately from a successful crate upload.

Proposed package descriptions:

| Field | Library | CLI |
| --- | --- | --- |
| Description | `Dependency-based PostgreSQL migrations with forward-only SQL and per-schema tracking.` | `Command-line PostgreSQL migrations with named dependencies and per-schema tracking.` |
| Repository | `https://github.com/kamysh/kryzhen` | `https://github.com/kamysh/kryzhen` |
| README | `../README.md` | `../README.md` |
| Keywords | `postgresql`, `migrations`, `database`, `schema`, `mallard` | The same five keywords |
| Categories | `database` | `database`, `command-line-utilities` |
| License | Preserve existing `Apache-2.0` | Preserve existing `Apache-2.0` |

This requires a crates.io account authorized to publish the names and a verified
email address. Use approved account access; do not put tokens in these files or
ask for them in public text. No account access has been checked in this stage.
The source packaging and build checks have not been run.

Rules: [Cargo publication guide](https://doc.rust-lang.org/cargo/reference/publishing.html),
[local dependencies in published packages](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html#local-paths-in-published-crates).

## Muninn and Mimir in the official MCP Registry

The registry is a public catalogue that other tool directories can read. Each
entry needs both a description and a supported way to install the software.
The descriptions are prepared in
[Muninn metadata](registry/muninn.metadata.json) and
[Mimir metadata](registry/mimir.metadata.json).

The proposed names are `io.github.kamysh/muninn` and `io.github.kamysh/mimir`.
Name availability and account ownership must be checked before publication.

The existing release workflows produce executable files or compressed archives.
Those archives are not yet the install bundles used by the registry's MCPB
option. MCPB is a format for packaging an MCP server with instructions about
how to launch it.

The recommended next preparation step is to assess and prepare that bundle
format around the existing executables. The assistant would:

- Select and verify actual release files for each advertised operating system
  and processor type; the inspected workflows cover Linux x86_64, Linux ARM64
  and Apple Silicon.
- Describe which executable starts the server, include the required files, and
  check the bundle in a compatible client before advertising support there.
- Keep database setup, credentials and Muninn's background indexing process
  explicit. Installing a server bundle alone does not prepare its database or
  guarantee useful searches. No system service or timer will be installed as
  an incidental packaging step.
- Use the actual public bundle address and its calculated file hash in the
  complete registry entry. The current draft files contain neither a fictional
  download nor a made-up hash.
- Verify account ownership, publish only after approval, and read the resulting
  entries back to check their text and installation details.

Publishing Rust source packages is another supported route, but it would require
preparing the internal dependencies for registry publication too. The MCPB
approach is a recommendation to review, not an implemented packaging decision.

Rules: [supported packages](https://modelcontextprotocol.io/registry/package-types),
[publisher instructions](https://modelcontextprotocol.io/registry/quickstart),
[bundle format](https://github.com/modelcontextprotocol/mcpb/blob/main/MANIFEST.md).

## Article sites and other lists

### The dev.to article website needs another check

DEV, at dev.to, is a website where programmers publish articles. The complete
drafts can be considered for publication through
[its editor](https://dev.to/new). Its current
[AI article rules](https://dev.to/guidelines-for-ai-assisted-articles-on-dev)
allow disclosure-based use while restricting promotion and brand-building.
The [new disclosure choices](https://dev.to/devteam/introducing-ai-disclosure-on-dev-tools-for-nuance-clarity-and-better-feeds-34mk/)
include fully automated writing; saying that an AI wrote an article does not
remove the other rules. These drafts were written by an agent, so that is the
honest category. Whether these particular technical articles qualify has not
been established; they have not been submitted or rejected.

Before any submission, the assistant must establish that the explanatory article
and its intended use fit the current rules. Otherwise use the project-hosted
article only. Do not assign the maintainer a rewrite or a commenting campaign.

If suitable and approved, use the article's GitHub address as its original-source
link and preserve its exact title and body. Suggested topic tags:

| Article | Tags |
| --- | --- |
| Kryzhen | `postgres`, `rust`, `database`, `abotwrotethis` |
| Muninn | `mcp`, `git`, `rust`, `abotwrotethis` |
| Mimir | `mcp`, `ai`, `rust`, `abotwrotethis` |

This needs an authorized DEV account. The documented
[publication API](https://developers.forem.com/api/v1#tag/articles/operation/createArticle)
supports title, Markdown body and original-source URL. Check the actual editor
or current API before setting the AI disclosure; do not invent a field name.
Neither an account nor a publication connection has been verified here.

### Lists held out of immediate submission

- **This Week in Rust:** current rules reject LLM-written articles and
  project/tooling-update PRs. No submission of these articles is planned.
- **Awesome Postgres:** its rules require established adoption and production
  use. A conditional entry is prepared, but those qualifications are unverified.
- **Awesome Rust:** its contribution guide requires popularity evidence, such
  as GitHub stars or crate downloads. Do not submit without checking eligibility;
  no such evidence was established in this stage.
- **PulseMCP:** a current submission form could not be verified. Do not treat
  guessed form addresses as a ready route.
- **HN, unsolicited outreach, paid promotion:** outside this plan.

Rules: [This Week in Rust](https://github.com/rust-lang/this-week-in-rust#readme),
[Awesome Postgres](https://github.com/dhamaniasad/awesome-postgres/blob/master/CONTRIBUTING.md),
[Awesome Rust](https://github.com/rust-unofficial/awesome-rust/blob/main/CONTRIBUTING.md).

## What counts as finished after publication

For each approved action, the assistant records the public address, date and
observed result. Check that the intended text is actually present, rather than
equating a successful command with a successful publication.

Keep four outcomes distinct: submitted, accepted, published and seen by readers.
The first three can be checked through public pages; reader attention needs
actual traffic information where available. No minimum reaction, visitor count
or new-user target is a prerequisite for publishing the remaining material.

For later releases, the assistant can reuse the approved project descriptions,
update only claims affected by the release, refresh changed installation links,
and prepare the next announcements. No recurring job or monitoring service has
been created.
