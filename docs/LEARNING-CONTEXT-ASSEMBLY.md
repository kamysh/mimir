# Learning-context response assembly

Learning context combines relevant beliefs, matching procedures, their observed outcomes and assessment groups. Every component uses the same read-only database snapshot. Displaying a procedure does not record its use or increase its success count.

`LearningContextProtocol.Assembly` describes the response after retrieval selects belief identities. It resolves those identities against the stored beliefs using the existing visibility, working-memory and superseded-belief rules. It computes matching procedures from their situations, ranks them by overlap and observed outcomes, and uses identity order for equal scores. Omitted selection includes every matching procedure.

Procedure counts come from current experience versions in the requested project. Tool results and user feedback can establish measured success or failure. Agent reports and unknown outcomes increase only the unknown count. Procedure provenance and assessments come from that same stored world. Assessment groups cover the selected beliefs without truncation; invalid stored assessments retain the existing explicit invalid-assessment outcome.

The shared read-only recovery constructor requires the exact derived answer and preservation of the entire application world, including graph records, history, vectors, documents and operation metadata. The procedure-snapshot law proves that ranking and explicit selection retain the derived counts and provenance.

This is an internal response-assembly proof, not an additional public request or the complete learning-context operation. The preceding belief-retrieval selection proof remains work under #132 and #135. This slice does not decide optional embedding behavior or claim that the mandatory dispatcher is already connected.
