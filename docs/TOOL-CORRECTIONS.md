# Correction is not completed work

A normal MCP response may ask the agent to fix its request. That is neither
completed business work nor an operation failure. For example, a missing
project asks for that project without running deletion or claiming that
deletion completed.

The handler model distinguishes completion, correction and operation failure.
A completed result still requires the decoded operation, its actual execution
and its projected answer. Unknown tools and invalid arguments produce a
correction through their checked admission result instead.

The general admission-correction law requires an empty application-event trace:
rejected input executes no operation at all. A completed operation cannot be
reclassified as an input correction. Converting that correction to its
ordinary tool response also requires the existing certificate that the full
stored world is unchanged; a diagnostic formatter cannot supply that evidence.
The complete correction report is retained in that response.

This law covers input rejected before execution. A later user decision after
embedding or grounding preparation is a separate workflow in #95–#100; it may
have performed reads and preparation while leaving the stored world unchanged.

The original #208 change connected the MCP handler and composition contracts
to this correction flow. Mandatory recovery dispatch and physical database
correspondence remain separate obligations in #74/#76/#153.

The judge also preserves these structured corrections when its own pure review
validation finds the problem before contacting MCP. For example, feedback that
names an undeclared candidate retains the full field path, the allowed target
forms and the suggested repair. The model can declare the intended candidate
and continue the same review dialogue. If it stops before fixing the request,
the report retains that correction as `needs_input`; no review is confirmed.
