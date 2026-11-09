# Judge work selection

One `mimir judge run` selects all currently eligible experiences in its project
scope. It sends no result count to `pending_experiences`. The query's omitted
count also means all matches; there is no second hidden default in that layer.
Each selected experience still receives its own revision-checked review.

`judge.batch_size` is retired, including in one-shot runs. Configuration checking
names the setting and directs the user to `mimir config upgrade`, followed by
`mimir config check`. The upgrade removes only the judge setting. It preserves
the project, MCP arguments, model choices, unrelated settings and comments. A
separately chosen embedding batch setting is not a judge quota and is preserved.

Selection reads the currently eligible set. Work arriving after that read belongs
to a subsequent run. Existing project, exclusion, deferred-revision, identity and
review-revision checks remain in force. Removing a count does not turn an idle
snapshot into proof of recovery or permit an unverified review to count as done.

The formal selection contract keeps eligibility, scope, unique identities and
source validity without a size predicate. The composed progress evidence names
the whole selected set rather than a prefix cut to a configured count.

The local regression uses a fake model with the real runner, MCP server and
disposable PostgreSQL database. It records 12 experiences, verifies all 12 saved
reviews in one run, and reads the queue back as empty for that project. No live
model account, configuration or deployment is used.

This addresses #162, following the query prerequisite in #229. Watcher scheduling
and the remaining interface/configuration restrictions have their separate issues.
