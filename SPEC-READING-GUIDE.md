# Reading the Mimir specification

Start with the operation you want to understand. The prose in each topic
explains the application behavior before the declarations that enforce it.
Follow the topic's links for the transaction and proof details.

| Topic | What it covers | Implementation checks |
| --- | --- | --- |
| [MCP requests and replies](spec/Mimir/McpApplicationComposition.lagda.md) | Request admission, correction guidance, and how app results become tool replies | MCP admission and connection tests |
| [Direct belief publication](spec/Mimir/BeliefEmbedding.lagda.md) and [beliefs from reviews](spec/Mimir/ReviewBeliefPreparation.lagda.md) | Which inputs must be prepared, where the UUID comes from, and when the complete belief is saved | PostgreSQL publication and MCP review tests |
| [Weighted evidence](spec/Mimir/GroundingPublication.lagda.md) and [reading citations](spec/Mimir/EvidenceRead.lagda.md) | What changes the belief, what records a source, and how citations are selected | Evidence rollback and MCP retrieval tests |
| [Document loading](spec/Mimir/DocumentLoading.lagda.md) and [document search](spec/Mimir/DocumentQuery.lagda.md) | Atomic replacement of an index and scoped search over its passages | PostgreSQL document replacement and search tests |
| [Belief search](spec/Mimir/RetrievalProtocol.lagda.md) and [learning context](spec/Mimir/LearningContextProtocol.lagda.md) | Eligibility, ranking, result selection, and semantic-search availability | MCP retrieval and learning-context tests |
| [Experience recording](spec/Mimir/ExperienceRecord.lagda.md), [review correction](spec/Mimir/ReviewRecord.lagda.md), and [history](spec/Mimir/LearningHistory.lagda.md) | Stable identity, versioned contributions, stale requests, and consistent history | MCP correction, learning-cycle, and PostgreSQL history tests |
| [Belief explanations](spec/Mimir/BeliefExplanation.lagda.md) and [lesson assessments](spec/Mimir/AssessmentRead.lagda.md) | Current provenance and links, active contribution selection, and assessment history | MCP explanation and assessment reads in the learning cycle |
| [Inference and retirement](spec/Mimir/InferenceProtocol.lagda.md) and [project deletion](spec/Mimir/ProjectDeletion.lagda.md) | Which beliefs change or are removed, and what happens after a failed write | PostgreSQL rollback and fresh-retry tests |
| [Judge watcher](spec/Mimir/JudgeHostProtocol.lagda.md) | Work selection, confirmation, deferral, outage recovery, and repair | Watcher unit tests and the isolated judge database recovery test |

The [formal coverage inventory](docs/FORMAL-BEHAVIOR-COVERAGE.md) describes the
broader specification and the [external guarantees](docs/FORMAL-EXTERNAL-GUARANTEES.md)
describe assumptions about dependencies. This guide covers the reader topics
listed above. Their Agda checks establish properties of the specification
under those assumptions. Rust correspondence is checked through the focused
implementation tests. A structural inventory check alone establishes that
the maintained operation mappings and imports exist.

When changing behavior, update the relevant reader contract, check its
connection through the application and update the focused Rust verification.
Keep observed limitations visible in the topic or its verification record.
CI type-checks and renders the aggregate, checks links to repository files,
and checks the formal inventory. Run the same reader check with
`nix develop --command bash scripts/formal/check-readers.sh`.
Run the isolated PostgreSQL publication and MCP tests with
`bash scripts/test-isolated.sh --check publication`.
