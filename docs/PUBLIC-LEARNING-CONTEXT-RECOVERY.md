# Public learning-context recovery

`PublicLearningContextRecovery` receives the context, explicit project and caller's optional positive result count. It accepts no selected beliefs, embeddings, procedure counts or desired answer.

A blank or whitespace-only project returns a normal request for correction before database or embedding work starts. The response names `project`, explains the nonblank requirement, and tells the caller to supply the intended value or ask the user. The native guard uses that same explanation. It does not invent a project, silently change the scope, or close the MCP connection.

For an admitted request, the operation composes the certified public search with the existing learning-context assembly. Its required `Operation.retrieval` field contains the complete search certificate, including the proof that the recorded backend/query reply was actually observed. Context assembly adds no effects to that trace and derives all additional values from the same stored snapshot.

The selected belief identities come from the world-derived search result. Procedures, measured outcome counts, provenance and assessment groups are then calculated by the existing `LearningContextProtocol.Assembly` functions. Agent reports and unknown outcomes remain separate from measured success and failure. Retrieval changes none of those stored observations and does not count as successful use. Stored invalid assessment values retain the existing explicit invalid-assessment outcome rather than being presented as valid scores.

General proofs require the complete calculated context and preservation of the entire application world after a completed retry. They also retain the exact observed request/backend transcript, keep procedure data tied to the same snapshot, and require the assessment-truncation flag to remain false. Omitted selection returns all matching records; only a caller's explicit positive selection applies.

Dispatcher work in #74 must accept the full request-specific context `Operation`, which itself retains the full retrieval certificate. Accepting only a `RecoverableFor` projection would lose this required evidence. The checked running state can still be built from the operation's recovery projection; the assembly input type must keep the complete certificate.

Rust statement correspondence and global dispatcher registration remain separate integration work. The focused native regressions cover the actual blank-project correction: a request must finish immediately while the snapshot connection is deliberately held, and an actual MCP connection must accept a corrected query afterward. They use no request timeout, model or account.
