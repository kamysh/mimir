# Publicity drafts for Kryzhen Muninn and Mimir

The three GitHub descriptions, README introductions and articles were published
and checked on 2026-10-20. The two software-list requests have been submitted:
[Muninn #17148](https://github.com/punkpeye/awesome-mcp-servers/pull/17148) and
[Mimir #17149](https://github.com/punkpeye/awesome-mcp-servers/pull/17149).
Both projects have now passed Glama's checks and appear in its public search.
Both Glama pages are public. The list requests remain open for the maintainers'
decision. See [public changes and submitted requests](publication-results.md)
for the public links and verification results.

The files contain clearer GitHub descriptions, one article about each project,
and requests to add Muninn and Mimir to a public software list. The assistant
handles the work after the relevant approval. No existing audience is assumed,
and the maintainer does not need to find users or write articles.

The GitHub text and articles were published without changing the software.
The additional Glama work was approved. Both test setups now pass local startup,
tool-listing and database-read checks. Both projects have been submitted to Glama
and approved. Ownership access, configuration submission and Glama checks are complete;
see [the test and submission report](glama/README.md).
Listing Kryzhen on crates.io, where Rust programmers
download libraries, needs changes to its package settings and a build check.
Listing Muninn and Mimir in the official MCP catalogue needs downloads prepared
with instructions about how an application should start each server. Those
technical changes have not been made.

Some websites suggested earlier have rules that prevent or restrict the planned
submissions. They are identified below and in the publication steps. A public
page or accepted listing does not establish that anyone has read it or tried
the software.

## Files to review

| Material | Contents |
| --- | --- |
| [Repository copy](repository-copy.md) | Exact About descriptions, topics, README introductions, related-project links and profile introduction |
| [Directory submissions](directory-submissions.md) | Submitted entries and request text for Muninn and Mimir; a conditional Kryzhen entry |
| [Muninn article](articles/muninn.md) | How code search selects a Git worktree while reusing unchanged content |
| [Mimir article](articles/mimir.md) | Preserving reasoning and correcting the evidence behind an agent memory |
| [Kryzhen article](articles/kryzhen.md) | Dependency-based PostgreSQL migrations applied independently to multiple schemas |
| [Publication queue](publication-queue.md) | Destinations, sequence, account requirements, technical prerequisites and completion receipts |
| [Verification](verification.md) | Claim sources, checks and remaining publication prerequisites |
| [Glama test setups](glama/README.md) | Submitted settings, successful local and Glama checks, and public search verification |
| [Approved publication checks](publication-checks.proposed.json) | The two README checks registered and passed for this temporary external checkout |
| [Nix publication results](nix/README.md) | Three project changes merged and verified; Nix search request #1602 submitted, awaiting acceptance |
| [mcp.so submissions](mcp-so/README.md) | Muninn #5968 and Mimir #5969 submitted through the official GitHub queue; exact text verified, website publication pending |
| [Muninn registry metadata](registry/muninn.metadata.json) | Proposed discovery fields, without an invented install package |
| [Mimir registry metadata](registry/mimir.metadata.json) | Proposed discovery fields, without an invented install package |

The article files are complete drafts and say that an AI assistant wrote them.
The two JSON files contain descriptions for a public software catalogue. They
are not ready to submit: the catalogue also needs a supported way to install
each tool, which still has to be prepared and checked.

## Publication steps

1. Publish the repository copy and articles as ordinary project documentation,
   update GitHub About/topics, and add the profile introduction if desired.
2. Submit the two prepared Awesome MCP Servers entries. They link existing
   repositories and do not depend on crates.io publication or new MCP packaging.
3. Consider publishing the articles on [dev.to](https://dev.to), a website for
   programmers, after checking its rules and account access. Its rules allow
   disclosed AI writing but restrict promotional use; whether these articles
   qualify has not been settled. The articles can be published on the project
   pages without that website.
4. Prepare and publish Kryzhen's library and CLI crates through a separately
   approved packaging stage. Verify the public crate pages and docs.rs results.
5. Prepare Muninn and Mimir MCP distribution metadata around actual supported
   artifacts, then publish to the official MCP Registry.

The repository pages, articles and MCP list submissions can proceed independently
of the registry packaging. There is no prescribed waiting period or requirement
to collect feedback before the next publication.

## Scope of the original preparation

All changes are confined to this directory in the Mimir checkout. The source
projects, existing READMEs, Cargo manifests, release workflows and installed
configuration are unchanged. No account credentials were inspected. The
existing uncommitted Kryzhen files were left untouched.

Subsequent approved publication changed the public GitHub pages as recorded in
[the results](publication-results.md). The approved Glama stage also built and
ran disposable test containers. No system settings, services or release workflows
were changed. Glama is complete; both software-list requests are submitted.
The final publication step added the explicitly approved two-check entry to
Codex's publication policy and preserved all other entries.

## Decisions already reflected in the material

- All three projects retain their names and existing purpose.
- Kryzhen is presented as a PostgreSQL tool and Rust library in its own right.
- Muninn and Mimir can be installed independently; their relationship is explained
  through short cross-links rather than a required suite installation.
- HN posting, cold outreach and user recruitment are excluded.
- No claims about adoption, speedups, token savings or guaranteed attention are
  invented. Visibility is reported with public URLs, accepted listings and any
  traffic actually observable after publication.
- This Week in Rust is excluded: its current rules reject LLM-written articles
  and project/tooling-update PR submissions. No human rewrite is assigned to the
  maintainer as a workaround.
- Awesome Postgres is conditional because its contribution rules require
  recognition, adoption and production use. The package does not assert that
  those requirements have been established for Kryzhen.
