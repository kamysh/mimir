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

This changes the existing MCP handler and composition contracts for #208. It
matches the already implemented correction flow and prepares the retention
policy precheck in #207. It does not complete the mandatory recovery dispatcher
or the remaining physical database correspondence in #74/#76/#153. Native
source is unchanged.
