# Beliefs need an embedding and an explicitly cited source

Before Mimir stores a new belief, the submitting agent must provide an indexed
document passage and explain why that passage supports the claim. A citation
contains the actual chunk ID returned by `query_document`, the exact document
path, an exact quotation from that chunk and the agent's explanation.

Mimir checks that the chunk exists, belongs to that document, has an indexed
vector and is compatible with the belief's project. It checks the quotation
against the stored text. The explanation must be present; it records the
agent's reasoning and does not constitute a mathematical proof of truth.
Similarity can rank passages suggested by a search. It cannot establish that a
passage supports a claim, and there is no similarity acceptance cutoff.

For example, a passage saying that a command returned an error can support a
belief about that observed error. A nearby passage about another command does
not become support merely because its embedding is similar. The agent must
choose and explain the actual supporting passage.

If a citation is missing, malformed, mismatched or no longer indexed, Mimir
returns correction guidance before storing the belief. The calling agent must
open the dialog when support is missing or unclear. It must not invent a
quotation, silently choose another source or omit the requirement. A valid
citation does not require a separate AI reviewer or a separate user approval
for each belief.

The configured embedding backend must then return exactly one complete,
finite, nonzero vector for the complete belief content. Mimir stores the
belief, vector, independent provenance and source references in one
transaction. A failed publication leaves none of that new business data
partially stored. Preparation ownership and diagnostics can exist before
publication. The embedding call stops if the preparation is cancelled, its
project is deleted, or a cited indexed passage changes or disappears.

Source references are stored separately from weighted evidence and are
returned as `sources` in enriched belief results and explanations. They have
no weight and do not change the belief's probability or confidence. Existing
manual weighted evidence keeps its existing meaning. Review assessments can
still change a candidate's probability through their separate, existing rules;
the source citation itself contributes nothing to that calculation. Indexing a
document no longer automatically asserts support for nearby beliefs.

The same source and embedding requirements apply to every newly created belief
candidate in `review_experience`. A stored experience alone is not an indexed
document passage. Existing immutable candidate declarations retain their exact
original form on replay; their history is not rewritten to add citations.

## Retrying an unfinished publication

The registered operation first saves PostgreSQL's preparation identity and
creation time. Repeating that step returns the same identity and time. The
final transaction saves its original result together with the publication.
A retry after a lost reply returns that result before starting another
embedding or inspecting changed provider settings. It cannot create a second
belief under the same token.

An unfinished operation remains bound to its original arguments and provider
identity. If those arguments are wrong, read its binding and saved outcome,
then ask the user before cancelling it and reserving corrected work. Mimir
neither rewrites a bound request nor cancels it automatically to get past a
problem. Missing citations in older stored declarations decode as an empty
list for replay compatibility; an empty list never permits new publication.

## What the checked model establishes

`IndependentPublicationRecovery.Registered.Public.fullOperation` contains the
whole-store recovery and progress proofs and the observation-receipt proof.
Its public input is the operation token. The source snapshot and embedding
response come from explicit execution effects, including the exact configured
backend and complete original content. They are not expected answers supplied
by a caller.

The publication goal fixes the entire represented store: the new belief,
vector, provenance and complete source list are published together; weighted
evidence and unrelated state remain unchanged. Both committed steps are
covered, including a commit whose acknowledgement was lost. A failed
preparation preserves the durable ownership step without marking publication
complete; a repaired prerequisite can therefore succeed on a later retry.

The mandatory application dispatcher and public token-interface wiring remain
the separate work in #74/#76 and #85–#86. That dispatcher must consume the full
certificate, including its observation proof, rather than only a projection of
its recovery theorem. Its request-specific assembly type must require
`IndependentPublicationRecovery.Registered.Public.Operation`. The source
snapshot and vector in the recovery goal are internal observations: the fixed
public script constructs its publication packet only after the corresponding
source-read and exact embedding effects. The public transaction relation binds
that read to the actual world. Converting the full certificate to a recovery
value keeps this script and transaction relation, but loses the explicit
observation-proof obligation and must not become an alternative registration
path. The durable-only helper certificate is private.

These Agda checks are a design certificate; they are not
a proof that compiled Rust refines Agda. The isolated database and MCP checks
provide separate implementation evidence.
