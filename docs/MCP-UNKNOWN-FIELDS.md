# Unknown argument fields

Tool argument records accept only their declared fields. Discovery advertises
`additionalProperties: false` for each record, including records inside arrays
and declared alternatives. Admission checks that same registered schema before
the business handler runs.

For example, `delete_project` with both `project` and `projet` returns a
correction and deletes nothing. `query_relevant` with `limt` does not ignore the
field and begin embedding with a default selection. A nested misspelling gets
its complete field path and the accepted names for that record. The caller
chooses the correction; the server never renames fields or executes a guessed
request.

A supplied record tag selects the corresponding declared record kind for
diagnostics. A belief record is not told to supply the fields of a pattern.
Missing or unknown tags require the caller to choose a supported alternative.
No field-list, diagnostic-count or string-size cut is introduced.

Unknown tool names receive the same actionable response with all advertised
names. Unknown `tools/call` parameters receive an invalid-parameters response;
the protocol's optional `_meta` member remains allowed.

The existing Agda request decoder has an exhaustive accepted-field table over
the closed tool type. A general theorem establishes that every successfully
decoded object has only accepted fields. Shared nested-record rejection now
uses the specific unknown-field diagnostic code. This does not claim that
native/model output correspondence or proof-backed dispatch is complete;
those remain the separate recovery binding and differential-test stages.

The process regression attempts deletion, pattern insertion and experience
replacement using misspelled fields. It then reads the original experience and
checks that no pattern was created, using the same connection and a disposable
database.
