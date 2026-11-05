# Mimir behavioral specification coverage

Current scope: **Mimir application behavior, with standard libraries supplied externally**.
The [value audit](FORMAL-VALUE-AUDIT.md) records the removal of library
implementation proofs and unused support. The verification dates and module
counts in the historical sections below describe those earlier snapshots.

This extends the existing specification for the current Mimir product. It covers public inputs and defaults, validation, output projections, state transitions, partial failures, persistence and background protocols. The specification-only completion receipt remains in FORMAL-BEHAVIOR-VERIFICATION.json. Subsequent Rust alignment is documented in [RUST-CONFORMANCE.md](RUST-CONFORMANCE.md); the checked model must not be described as a verified installed binary.

The inventory contains **34 MCP tools, 30 CLI leaf commands, seven lifecycle groups and 61 source artifacts** (38 production Rust files, ten SQL migrations, and 13 verification/test/example artifacts). Core-library-only entry points are listed separately below.

## Reading the contract

`PublicRequest` supplies concrete input decoding; `ApplicationProtocol` dispatches to the operation protocols; `ApplicationOutput` and `PublicEncoding` specify observable result shapes. `McpToolExecution`, `McpApplicationComposition` and `McpRuntimeComposition` connect those operations to the MCP exchange and byte stream. `McpServiceProcess` includes core configuration, migrations and startup. `CLI`, `CLIServiceBinding`, `CLIReembed` and `HookProtocol` specify the existing command paths.

Protocols distinguish application decisions from external observations. Database, filesystem, network and subprocess replies retain failure and uncertain outcomes. Their concrete application meanings are supplied by the storage, transaction, publication, codec and lifecycle modules listed below; they are not unrestricted successful application callbacks. A `Runs` control transcript alone is not a Rust conformance proof or proof that real I/O happened.

## Stored belief evidence

[EvidenceValidity](../spec/Mimir/EvidenceValidity.agda) defines valid stored
beliefs. Both current evidence counts and the original prior counts must be
finite and nonnegative, and each pair must have a finite total. Displayed
probability and confidence must stay between zero and one. Empty evidence is
allowed: its probability is one half and its confidence is zero. A normal
displayed probability cannot make negative or overflowing counts valid.

[StoreRows](../spec/Mimir/StoreRows.agda) proves that every successful belief
read satisfies these rules. Only absent legacy evidence fields use the
documented fallback: missing original counts come from the stored probability
and confidence; missing current counts use those original counts. A supplied
malformed, negative, infinite or NaN count is refused. A pair whose addition
overflows is also refused. This specifies refusal, not repair of stored data.

[PosteriorComputation](../spec/Mimir/PosteriorComputation.agda) checks inputs,
each calculated update before change detection, and the final state. Numeric
failure is distinct from an empty successful update. Decay checks its result
before deciding whether the change is large enough to save. The propagation
and review paths refuse numeric failures instead of reporting success.

[LearningRecompute](../spec/Mimir/LearningRecompute.agda) proves that applying
valid updates preserves valid beliefs and retains every original prior count.
[StorageSemantics](../spec/Mimir/StorageSemantics.agda) requires valid evidence
for inserted beliefs and posterior writes. Its preservation laws cover commit,
abort and either possible outcome after a lost acknowledgement. These laws
assume the unchanged starting beliefs were valid; they do not claim that an
update repairs unrelated damaged records.

Arithmetic and parsing remain supplied library operations. These are checks
and general laws about Mimir's accepted values and updates, not proofs of
floating-point arithmetic or a parser implementation. The change is confined
to the specification; it does not certify or change the installed application.

## Behavioral areas

| Area | Detailed behavior |
| --- | --- |
| Experiences and reviews | Stable incident/item ownership, revision admission, exact retries, immutable history, correction/retraction, candidate identity and provenance, active edge/contribution replacement, numeric recomputation, locked fresh reads, commit/abort/lost acknowledgement. |
| Assessments and learning context | Separate correctness/usefulness calculations, scope/rubric selection, active/stale history, observed outcome counts, bounded evidence indices, pattern ranking, retrieval without recording successful use. |
| Graph and inference | Record defaults and legacy decoding, inserts and edge effects, deletion cleanup, complete dependency closure, fixed priors, seed clamping, 50-iteration exit, operation order, memory-specific decay, expiry and causal intervention. |
| Retrieval | Project/global filtering, working-memory exclusion, lexical tokens, physical vector selection, weighted binary32 RRF, type preference, deterministic ordering, zero/nonzero limits, grounding and evidence joins. |
| Documents and embeddings | Markdown chunk/parent construction, path reads, configured remote/local backend lifecycle, cache/download/load failures, batch cardinality/index/dimension association, paired publication, query parent context and automatic grounding. |
| Judge | Configuration, one owned MCP client, handshake/catalog/capabilities, shared ID/deadline including overflow, pending/deferred selection, scoped tools, API/subprocess model exchanges, budgets, trace barriers, reread confirmation, durable finalization, cleanup, watch/backoff and stop at the wait point. |
| Notifications | Independent notifier API, admission, exclusive outbox lock, incident/recovery reconciliation, reservations, retries and delivery uncertainty, bounded durable files, exact record decoding, SMTP, OAuth identity/cache/refresh ordering, read-only digest snapshot and cursor advancement. |
| Startup and migrations | Core operation without judge/model settings, source/override precedence, credential/TLS selection, all ten DDL/data bodies, historical item ownership preservation, database-assigned item IDs, local-key constraints, migration dependencies, history/checksum/locking and transaction outcomes. |

## MCP operations

Every operation below also uses the shared input/dispatch/output/MCP composition described above. The machine-readable map retains native dispatch locations, interface evidence, the original gap and all completion modules.

| Operation | Application modules |
| --- | --- |
| `insert_belief` | [GraphRecords](../spec/Mimir/GraphRecords.agda), [GraphWrites](../spec/Mimir/GraphWrites.agda), [GraphMutationProtocol](../spec/Mimir/GraphMutationProtocol.agda), [BeliefEmbedding](../spec/Mimir/BeliefEmbedding.agda), [BeliefEmbeddingStorage](../spec/Mimir/BeliefEmbeddingStorage.agda), [EmbeddingService](../spec/Mimir/EmbeddingService.agda), [GroundingStorageBinding](../spec/Mimir/GroundingStorageBinding.agda) |
| `delete_belief` | [GraphDeletion](../spec/Mimir/GraphDeletion.agda), [ProjectDeletion](../spec/Mimir/ProjectDeletion.agda), [StorageSemantics](../spec/Mimir/StorageSemantics.agda), [ApplicationStore](../spec/Mimir/ApplicationStore.agda) |
| `delete_project` | [GraphDeletion](../spec/Mimir/GraphDeletion.agda), [ProjectDeletion](../spec/Mimir/ProjectDeletion.agda), [StorageSemantics](../spec/Mimir/StorageSemantics.agda), [ApplicationStore](../spec/Mimir/ApplicationStore.agda) |
| `delete_pattern` | [GraphDeletion](../spec/Mimir/GraphDeletion.agda), [ProjectDeletion](../spec/Mimir/ProjectDeletion.agda), [StorageSemantics](../spec/Mimir/StorageSemantics.agda), [ApplicationStore](../spec/Mimir/ApplicationStore.agda) |
| `insert_pattern` | [GraphRecords](../spec/Mimir/GraphRecords.agda), [GraphWrites](../spec/Mimir/GraphWrites.agda), [GraphMutationProtocol](../spec/Mimir/GraphMutationProtocol.agda), [BeliefEmbedding](../spec/Mimir/BeliefEmbedding.agda), [BeliefEmbeddingStorage](../spec/Mimir/BeliefEmbeddingStorage.agda), [EmbeddingService](../spec/Mimir/EmbeddingService.agda), [GroundingStorageBinding](../spec/Mimir/GroundingStorageBinding.agda) |
| `record_support` | [GraphMutationProtocol](../spec/Mimir/GraphMutationProtocol.agda), [GraphWrites](../spec/Mimir/GraphWrites.agda), [InferenceProtocol](../spec/Mimir/InferenceProtocol.agda), [InferenceStorageBinding](../spec/Mimir/InferenceStorageBinding.agda), [PosteriorComputation](../spec/Mimir/PosteriorComputation.agda) |
| `record_cause` | [GraphMutationProtocol](../spec/Mimir/GraphMutationProtocol.agda), [GraphWrites](../spec/Mimir/GraphWrites.agda), [InferenceProtocol](../spec/Mimir/InferenceProtocol.agda), [InferenceStorageBinding](../spec/Mimir/InferenceStorageBinding.agda), [PosteriorComputation](../spec/Mimir/PosteriorComputation.agda) |
| `record_defeat` | [GraphMutationProtocol](../spec/Mimir/GraphMutationProtocol.agda), [GraphWrites](../spec/Mimir/GraphWrites.agda), [InferenceProtocol](../spec/Mimir/InferenceProtocol.agda), [InferenceStorageBinding](../spec/Mimir/InferenceStorageBinding.agda), [PosteriorComputation](../spec/Mimir/PosteriorComputation.agda) |
| `record_contradiction` | [GraphMutationProtocol](../spec/Mimir/GraphMutationProtocol.agda), [GraphWrites](../spec/Mimir/GraphWrites.agda), [InferenceProtocol](../spec/Mimir/InferenceProtocol.agda), [InferenceStorageBinding](../spec/Mimir/InferenceStorageBinding.agda), [PosteriorComputation](../spec/Mimir/PosteriorComputation.agda) |
| `get_belief` | [GraphReadProtocol](../spec/Mimir/GraphReadProtocol.agda), [GraphRecords](../spec/Mimir/GraphRecords.agda), [StorageReadBinding](../spec/Mimir/StorageReadBinding.agda), [StoreRows](../spec/Mimir/StoreRows.agda) |
| `list_beliefs` | [GraphReadProtocol](../spec/Mimir/GraphReadProtocol.agda), [GraphRecords](../spec/Mimir/GraphRecords.agda), [StorageReadBinding](../spec/Mimir/StorageReadBinding.agda), [StoreRows](../spec/Mimir/StoreRows.agda) |
| `list_patterns` | [GraphReadProtocol](../spec/Mimir/GraphReadProtocol.agda), [GraphRecords](../spec/Mimir/GraphRecords.agda), [StorageReadBinding](../spec/Mimir/StorageReadBinding.agda), [StoreRows](../spec/Mimir/StoreRows.agda) |
| `get_contradictions` | [InferenceProtocol](../spec/Mimir/InferenceProtocol.agda), [InferenceStorageBinding](../spec/Mimir/InferenceStorageBinding.agda), [GraphNumerics](../spec/Mimir/GraphNumerics.agda), [PosteriorComputation](../spec/Mimir/PosteriorComputation.agda), [GraphPaths](../spec/Mimir/GraphPaths.agda) |
| `decay_all` | [InferenceProtocol](../spec/Mimir/InferenceProtocol.agda), [InferenceStorageBinding](../spec/Mimir/InferenceStorageBinding.agda), [GraphNumerics](../spec/Mimir/GraphNumerics.agda), [PosteriorComputation](../spec/Mimir/PosteriorComputation.agda), [GraphPaths](../spec/Mimir/GraphPaths.agda) |
| `sweep_expired_defeated` | [InferenceProtocol](../spec/Mimir/InferenceProtocol.agda), [InferenceStorageBinding](../spec/Mimir/InferenceStorageBinding.agda), [GraphNumerics](../spec/Mimir/GraphNumerics.agda), [PosteriorComputation](../spec/Mimir/PosteriorComputation.agda), [GraphPaths](../spec/Mimir/GraphPaths.agda) |
| `query_relevant` | [RetrievalProtocol](../spec/Mimir/RetrievalProtocol.agda), [RetrievalRanking](../spec/Mimir/RetrievalRanking.agda), [RetrievalReadContract](../spec/Mimir/RetrievalReadContract.agda), [StorageReadBinding](../spec/Mimir/StorageReadBinding.agda), [EvidenceRead](../spec/Mimir/EvidenceRead.agda) |
| `add_evidence` | [EvidenceRead](../spec/Mimir/EvidenceRead.agda), [GroundingPublication](../spec/Mimir/GroundingPublication.agda), [GroundingProtocol](../spec/Mimir/GroundingProtocol.agda), [StorageReadBinding](../spec/Mimir/StorageReadBinding.agda), [StorageSemantics](../spec/Mimir/StorageSemantics.agda) |
| `get_evidence` | [EvidenceRead](../spec/Mimir/EvidenceRead.agda), [GroundingPublication](../spec/Mimir/GroundingPublication.agda), [GroundingProtocol](../spec/Mimir/GroundingProtocol.agda), [StorageReadBinding](../spec/Mimir/StorageReadBinding.agda), [StorageSemantics](../spec/Mimir/StorageSemantics.agda) |
| `propagate_from` | [InferenceProtocol](../spec/Mimir/InferenceProtocol.agda), [InferenceStorageBinding](../spec/Mimir/InferenceStorageBinding.agda), [GraphNumerics](../spec/Mimir/GraphNumerics.agda), [PosteriorComputation](../spec/Mimir/PosteriorComputation.agda), [GraphPaths](../spec/Mimir/GraphPaths.agda) |
| `query_intervention` | [InferenceProtocol](../spec/Mimir/InferenceProtocol.agda), [InferenceStorageBinding](../spec/Mimir/InferenceStorageBinding.agda), [GraphNumerics](../spec/Mimir/GraphNumerics.agda), [PosteriorComputation](../spec/Mimir/PosteriorComputation.agda), [GraphPaths](../spec/Mimir/GraphPaths.agda) |
| `load_document` | [DocumentLoading](../spec/Mimir/DocumentLoading.agda), [DocumentPublication](../spec/Mimir/DocumentPublication.agda), [DocumentQuery](../spec/Mimir/DocumentQuery.agda), [GroundingProtocol](../spec/Mimir/GroundingProtocol.agda), [EmbeddingService](../spec/Mimir/EmbeddingService.agda), [StorageSemantics](../spec/Mimir/StorageSemantics.agda), [StorageReadBinding](../spec/Mimir/StorageReadBinding.agda) |
| `query_document` | [DocumentLoading](../spec/Mimir/DocumentLoading.agda), [DocumentPublication](../spec/Mimir/DocumentPublication.agda), [DocumentQuery](../spec/Mimir/DocumentQuery.agda), [GroundingProtocol](../spec/Mimir/GroundingProtocol.agda), [EmbeddingService](../spec/Mimir/EmbeddingService.agda), [StorageSemantics](../spec/Mimir/StorageSemantics.agda), [StorageReadBinding](../spec/Mimir/StorageReadBinding.agda) |
| `clear_document` | [DocumentLoading](../spec/Mimir/DocumentLoading.agda), [DocumentPublication](../spec/Mimir/DocumentPublication.agda), [DocumentQuery](../spec/Mimir/DocumentQuery.agda), [GroundingProtocol](../spec/Mimir/GroundingProtocol.agda), [EmbeddingService](../spec/Mimir/EmbeddingService.agda), [StorageSemantics](../spec/Mimir/StorageSemantics.agda), [StorageReadBinding](../spec/Mimir/StorageReadBinding.agda) |
| `get_learning_review` | [LearningOperations](../spec/Mimir/LearningOperations.agda), [ReviewNumericalPublication](../spec/Mimir/ReviewNumericalPublication.agda), [ReviewPreparationPublication](../spec/Mimir/ReviewPreparationPublication.agda), [LearningTransaction](../spec/Mimir/LearningTransaction.agda), [LearningTransactionReceipt](../spec/Mimir/LearningTransactionReceipt.agda), [LearningQueryProtocol](../spec/Mimir/LearningQueryProtocol.agda), [LearningQueryBinding](../spec/Mimir/LearningQueryBinding.agda) |
| `learning_capabilities` | [LearningCapabilities](../spec/Mimir/LearningCapabilities.agda), [JudgeToolCatalogue](../spec/Mimir/JudgeToolCatalogue.agda) |
| `get_lesson_assessment` | [LearningAssessmentQueries](../spec/Mimir/LearningAssessmentQueries.agda), [AssessmentScores](../spec/Mimir/AssessmentScores.agda), [AssessmentSelection](../spec/Mimir/AssessmentSelection.agda), [AssessmentHistory](../spec/Mimir/AssessmentHistory.agda), [LearningQueryProtocol](../spec/Mimir/LearningQueryProtocol.agda), [LearningQueryBinding](../spec/Mimir/LearningQueryBinding.agda) |
| `lesson_assessment_history` | [LearningAssessmentQueries](../spec/Mimir/LearningAssessmentQueries.agda), [AssessmentScores](../spec/Mimir/AssessmentScores.agda), [AssessmentSelection](../spec/Mimir/AssessmentSelection.agda), [AssessmentHistory](../spec/Mimir/AssessmentHistory.agda), [LearningQueryProtocol](../spec/Mimir/LearningQueryProtocol.agda), [LearningQueryBinding](../spec/Mimir/LearningQueryBinding.agda) |
| `explain_belief` | [LearningQueryProtocol](../spec/Mimir/LearningQueryProtocol.agda), [LearningStore](../spec/Mimir/LearningStore.agda), [IndependentProvenance](../spec/Mimir/IndependentProvenance.agda), [CandidateRegistry](../spec/Mimir/CandidateRegistry.agda), [LearningQueryBinding](../spec/Mimir/LearningQueryBinding.agda) |
| `record_experience` | [LearningOperations](../spec/Mimir/LearningOperations.agda), [LearningPublication](../spec/Mimir/LearningPublication.agda), [LearningRevision](../spec/Mimir/LearningRevision.agda), [LearningHistory](../spec/Mimir/LearningHistory.agda), [LearningTransaction](../spec/Mimir/LearningTransaction.agda), [LearningTransactionReceipt](../spec/Mimir/LearningTransactionReceipt.agda), [LearningQueryProtocol](../spec/Mimir/LearningQueryProtocol.agda), [LearningHistoryWire](../spec/Mimir/LearningHistoryWire.agda), [LearningQueryBinding](../spec/Mimir/LearningQueryBinding.agda) |
| `pending_experiences` | [PendingSelection](../spec/Mimir/PendingSelection.agda), [LearningQueryProtocol](../spec/Mimir/LearningQueryProtocol.agda), [LearningHistoryWire](../spec/Mimir/LearningHistoryWire.agda), [LearningQueryBinding](../spec/Mimir/LearningQueryBinding.agda) |
| `review_experience` | [LearningOperations](../spec/Mimir/LearningOperations.agda), [ReviewNumericalPublication](../spec/Mimir/ReviewNumericalPublication.agda), [ReviewPreparationPublication](../spec/Mimir/ReviewPreparationPublication.agda), [LearningTransaction](../spec/Mimir/LearningTransaction.agda), [LearningTransactionReceipt](../spec/Mimir/LearningTransactionReceipt.agda), [LearningQueryProtocol](../spec/Mimir/LearningQueryProtocol.agda), [LearningQueryBinding](../spec/Mimir/LearningQueryBinding.agda) |
| `get_experience` | [LearningOperations](../spec/Mimir/LearningOperations.agda), [LearningPublication](../spec/Mimir/LearningPublication.agda), [LearningRevision](../spec/Mimir/LearningRevision.agda), [LearningHistory](../spec/Mimir/LearningHistory.agda), [LearningTransaction](../spec/Mimir/LearningTransaction.agda), [LearningTransactionReceipt](../spec/Mimir/LearningTransactionReceipt.agda), [LearningQueryProtocol](../spec/Mimir/LearningQueryProtocol.agda), [LearningHistoryWire](../spec/Mimir/LearningHistoryWire.agda), [LearningQueryBinding](../spec/Mimir/LearningQueryBinding.agda) |
| `experience_history` | [LearningOperations](../spec/Mimir/LearningOperations.agda), [LearningPublication](../spec/Mimir/LearningPublication.agda), [LearningRevision](../spec/Mimir/LearningRevision.agda), [LearningHistory](../spec/Mimir/LearningHistory.agda), [LearningTransaction](../spec/Mimir/LearningTransaction.agda), [LearningTransactionReceipt](../spec/Mimir/LearningTransactionReceipt.agda), [LearningQueryProtocol](../spec/Mimir/LearningQueryProtocol.agda), [LearningHistoryWire](../spec/Mimir/LearningHistoryWire.agda), [LearningQueryBinding](../spec/Mimir/LearningQueryBinding.agda) |
| `query_learning_context` | [LearningContextProtocol](../spec/Mimir/LearningContextProtocol.agda), [LearningContext](../spec/Mimir/LearningContext.agda), [LearningAssessmentQueries](../spec/Mimir/LearningAssessmentQueries.agda), [RetrievalProtocol](../spec/Mimir/RetrievalProtocol.agda), [RetrievalRanking](../spec/Mimir/RetrievalRanking.agda), [StorageReadBinding](../spec/Mimir/StorageReadBinding.agda) |

## CLI commands

| Command | Application modules |
| --- | --- |
| `init` | [ConfigurationInput](../spec/Mimir/ConfigurationInput.agda), [ConfigurationValues](../spec/Mimir/ConfigurationValues.agda), [ConfigurationProtocol](../spec/Mimir/ConfigurationProtocol.agda), [ConfigurationIO](../spec/Mimir/ConfigurationIO.agda) |
| `stats` | [GraphReadProtocol](../spec/Mimir/GraphReadProtocol.agda), [GraphRecords](../spec/Mimir/GraphRecords.agda) |
| `list` | [GraphReadProtocol](../spec/Mimir/GraphReadProtocol.agda), [GraphRecords](../spec/Mimir/GraphRecords.agda) |
| `patterns` | [GraphReadProtocol](../spec/Mimir/GraphReadProtocol.agda), [GraphRecords](../spec/Mimir/GraphRecords.agda) |
| `query` | [RetrievalProtocol](../spec/Mimir/RetrievalProtocol.agda), [RetrievalRanking](../spec/Mimir/RetrievalRanking.agda), [EvidenceRead](../spec/Mimir/EvidenceRead.agda) |
| `forget` | [ProjectDeletion](../spec/Mimir/ProjectDeletion.agda), [GraphWrites](../spec/Mimir/GraphWrites.agda) |
| `decay` | [InferenceProtocol](../spec/Mimir/InferenceProtocol.agda), [GraphNumerics](../spec/Mimir/GraphNumerics.agda) |
| `contradictions` | [InferenceProtocol](../spec/Mimir/InferenceProtocol.agda), [GraphNumerics](../spec/Mimir/GraphNumerics.agda) |
| `sweep-defeated` | [InferenceProtocol](../spec/Mimir/InferenceProtocol.agda), [GraphNumerics](../spec/Mimir/GraphNumerics.agda), [GraphDeletion](../spec/Mimir/GraphDeletion.agda) |
| `reembed` | [CLIReembed](../spec/Mimir/CLIReembed.agda), [BeliefEmbedding](../spec/Mimir/BeliefEmbedding.agda), [BeliefEmbeddingStorage](../spec/Mimir/BeliefEmbeddingStorage.agda), [EmbeddingService](../spec/Mimir/EmbeddingService.agda) |
| `intervene` | [InferenceProtocol](../spec/Mimir/InferenceProtocol.agda), [GraphNumerics](../spec/Mimir/GraphNumerics.agda), [PosteriorComputation](../spec/Mimir/PosteriorComputation.agda) |
| `evidence add` | [GroundingPublication](../spec/Mimir/GroundingPublication.agda), [GroundingProtocol](../spec/Mimir/GroundingProtocol.agda) |
| `evidence list` | [EvidenceRead](../spec/Mimir/EvidenceRead.agda), [StorageReadBinding](../spec/Mimir/StorageReadBinding.agda) |
| `delete belief` | [GraphDeletion](../spec/Mimir/GraphDeletion.agda) |
| `delete pattern` | [GraphDeletion](../spec/Mimir/GraphDeletion.agda) |
| `doc load` | [DocumentLoading](../spec/Mimir/DocumentLoading.agda), [DocumentPublication](../spec/Mimir/DocumentPublication.agda), [EmbeddingService](../spec/Mimir/EmbeddingService.agda) |
| `doc query` | [DocumentQuery](../spec/Mimir/DocumentQuery.agda), [StorageReadBinding](../spec/Mimir/StorageReadBinding.agda) |
| `doc clear` | [DocumentLoading](../spec/Mimir/DocumentLoading.agda), [DocumentPublication](../spec/Mimir/DocumentPublication.agda) |
| `hook prompt` | [HookProtocol](../spec/Mimir/HookProtocol.agda), [CLIServiceBinding](../spec/Mimir/CLIServiceBinding.agda) |
| `hook pretooluse` | [HookProtocol](../spec/Mimir/HookProtocol.agda), [CLIServiceBinding](../spec/Mimir/CLIServiceBinding.agda) |
| `hook stop` | [HookProtocol](../spec/Mimir/HookProtocol.agda), [CLIServiceBinding](../spec/Mimir/CLIServiceBinding.agda) |
| `hook set-project` | [HookProtocol](../spec/Mimir/HookProtocol.agda), [CLIServiceBinding](../spec/Mimir/CLIServiceBinding.agda) |
| `judge check-config` | [JudgeHostProtocol](../spec/Mimir/JudgeHostProtocol.agda), [JudgeConfigurationComposition](../spec/Mimir/JudgeConfigurationComposition.agda) |
| `judge run` | [JudgeHostProtocol](../spec/Mimir/JudgeHostProtocol.agda), [JudgeWorkflowComposition](../spec/Mimir/JudgeWorkflowComposition.agda), [JudgeBackendComposition](../spec/Mimir/JudgeBackendComposition.agda), [JudgeFinalizationComposition](../spec/Mimir/JudgeFinalizationComposition.agda) |
| `judge watch` | [JudgeHostProtocol](../spec/Mimir/JudgeHostProtocol.agda), [JudgeDigestComposition](../spec/Mimir/JudgeDigestComposition.agda), [JudgeDigestSnapshot](../spec/Mimir/JudgeDigestSnapshot.agda), [NotificationComposition](../spec/Mimir/NotificationComposition.agda) |
| `judge status` | [JudgeStatusProtocol](../spec/Mimir/JudgeStatusProtocol.agda), [JudgeStateOperations](../spec/Mimir/JudgeStateOperations.agda) |
| `judge diagnostics` | [JudgeStatusProtocol](../spec/Mimir/JudgeStatusProtocol.agda), [JudgeStateOperations](../spec/Mimir/JudgeStateOperations.agda) |

## Core library and persistence adapters

| Entry points or behavior | Modules |
| --- | --- |
| delete_evidence | [PublicRequest](../spec/Mimir/PublicRequest.agda), [ApplicationProtocol](../spec/Mimir/ApplicationProtocol.agda), [GroundingPublication](../spec/Mimir/GroundingPublication.agda), [GroundingProtocol](../spec/Mimir/GroundingProtocol.agda) |
| get_pattern, unscoped creation, scalar graph/inference helpers | [GraphReadProtocol](../spec/Mimir/GraphReadProtocol.agda), [GraphRecords](../spec/Mimir/GraphRecords.agda), [GraphMutationProtocol](../spec/Mimir/GraphMutationProtocol.agda), [CoreLibrary](../spec/Mimir/CoreLibrary.agda) |
| legacy AGE row decoding and prepared-query lifecycle | [StoreRows](../spec/Mimir/StoreRows.agda), [AgeQueryProtocol](../spec/Mimir/AgeQueryProtocol.agda) |
| physical vector writes, automatic grounding and reembedding | [BeliefEmbeddingStorage](../spec/Mimir/BeliefEmbeddingStorage.agda), [EmbeddingService](../spec/Mimir/EmbeddingService.agda), [GroundingStorageBinding](../spec/Mimir/GroundingStorageBinding.agda), [CLIReembed](../spec/Mimir/CLIReembed.agda) |
| configuration diagnostic projection | [CoreLibrary](../spec/Mimir/CoreLibrary.agda) |

## Lifecycle composition

| Lifecycle | Modules |
| --- | --- |
| MCP startup and request loop | [McpServiceProcess](../spec/Mimir/McpServiceProcess.agda), [McpRuntimeComposition](../spec/Mimir/McpRuntimeComposition.agda), [McpApplicationComposition](../spec/Mimir/McpApplicationComposition.agda), [McpToolExecution](../spec/Mimir/McpToolExecution.agda), [PublicRequest](../spec/Mimir/PublicRequest.agda), [ApplicationProtocol](../spec/Mimir/ApplicationProtocol.agda), [ApplicationOutput](../spec/Mimir/ApplicationOutput.agda), [PublicEncoding](../spec/Mimir/PublicEncoding.agda) |
| Configuration, connection and credentials | [ConfigurationProtocol](../spec/Mimir/ConfigurationProtocol.agda), [ConfigurationSchema](../spec/Mimir/ConfigurationSchema.agda), [ConfigurationValues](../spec/Mimir/ConfigurationValues.agda), [ConnectionProtocol](../spec/Mimir/ConnectionProtocol.agda), [Password](../spec/Mimir/Password.agda), [TLS](../spec/Mimir/TLS.agda), [ServiceStartup](../spec/Mimir/ServiceStartup.agda), [ServiceConnection](../spec/Mimir/ServiceConnection.agda), [CoreLibrary](../spec/Mimir/CoreLibrary.agda) |
| Database bootstrap and ten schema migrations | [MigrationSchema](../spec/Mimir/MigrationSchema.agda), [MigrationScriptBinding](../spec/Mimir/MigrationScriptBinding.agda), [ItemOwnerBackfill](../spec/Mimir/ItemOwnerBackfill.agda), [MigrationRuntime](../spec/Mimir/MigrationRuntime.agda), [MigrationComposition](../spec/Mimir/MigrationComposition.agda), [MigrationHistory](../spec/Mimir/MigrationHistory.agda) |
| Judge host, provider and subprocess lifecycle | [JudgeHostProtocol](../spec/Mimir/JudgeHostProtocol.agda), [JudgeWorkflowComposition](../spec/Mimir/JudgeWorkflowComposition.agda), [JudgeBackendComposition](../spec/Mimir/JudgeBackendComposition.agda), [JudgeClientStartup](../spec/Mimir/JudgeClientStartup.agda), [JudgeMcpLifecycle](../spec/Mimir/JudgeMcpLifecycle.agda), [JudgeAPIAdapter](../spec/Mimir/JudgeAPIAdapter.agda), [JudgeHarnessAdapter](../spec/Mimir/JudgeHarnessAdapter.agda), [JudgePersistenceComposition](../spec/Mimir/JudgePersistenceComposition.agda), [JudgeFinalizationComposition](../spec/Mimir/JudgeFinalizationComposition.agda) |
| Notification, digest and OAuth lifecycle | [JudgeDigestComposition](../spec/Mimir/JudgeDigestComposition.agda), [JudgeDigestSnapshot](../spec/Mimir/JudgeDigestSnapshot.agda), [NotificationComposition](../spec/Mimir/NotificationComposition.agda), [NotificationRuntime](../spec/Mimir/NotificationRuntime.agda), [NotificationFileBinding](../spec/Mimir/NotificationFileBinding.agda), [NotificationCodec](../spec/Mimir/NotificationCodec.agda), [NotificationWire](../spec/Mimir/NotificationWire.agda), [NotificationMail](../spec/Mimir/NotificationMail.agda), [OAuthComposition](../spec/Mimir/OAuthComposition.agda), [OAuthResponseBinding](../spec/Mimir/OAuthResponseBinding.agda), [SMTPProtocol](../spec/Mimir/SMTPProtocol.agda) |
| Embedding backend and automatic grounding | [EmbeddingService](../spec/Mimir/EmbeddingService.agda), [EmbeddingLifecycle](../spec/Mimir/EmbeddingLifecycle.agda), [EmbeddingBackend](../spec/Mimir/EmbeddingBackend.agda), [EmbeddingBatch](../spec/Mimir/EmbeddingBatch.agda), [BeliefEmbeddingStorage](../spec/Mimir/BeliefEmbeddingStorage.agda), [GroundingStorageBinding](../spec/Mimir/GroundingStorageBinding.agda), [DocumentLoading](../spec/Mimir/DocumentLoading.agda) |
| Experience/review concurrency and recovery | [LearningTransaction](../spec/Mimir/LearningTransaction.agda), [LearningTransactionReceipt](../spec/Mimir/LearningTransactionReceipt.agda), [LearningOperations](../spec/Mimir/LearningOperations.agda), [LearningPublication](../spec/Mimir/LearningPublication.agda), [ReviewNumericalPublication](../spec/Mimir/ReviewNumericalPublication.agda), [ReviewPreparationPublication](../spec/Mimir/ReviewPreparationPublication.agda), [DatabaseTransaction](../spec/Mimir/DatabaseTransaction.agda), [DatabaseAdvisoryLock](../spec/Mimir/DatabaseAdvisoryLock.agda), [DatabaseReadCommitted](../spec/Mimir/DatabaseReadCommitted.agda), [LearningQueryBinding](../spec/Mimir/LearningQueryBinding.agda) |

## Dependency and proof boundaries

- Standard Float/formatter, JSON/TOML, Unicode, UUID, clock, filesystem, TLS/HTTP/SMTP, tokenizer/ONNX, hashing, PostgreSQL and pgvector operations remain explicit dependency contracts. The specification defines Mimir’s choices, parameters, sequencing and handling of their results. It does not redevelop those libraries.
- All modules under `spec/` use `--safe` and are reachable from `Mimir.agda`. There are no postulates, holes or termination escape markers in that source tree.
- The three individually approved PostgreSQL postulates remain isolated in `assumptions/Mimir/Assumptions/PostgreSQL.agda`; the safe root does not import them. No new postulate was added in this bounded task.
- Legacy ideal/percentage models retain their structural laws. Current floating calculations and operation behavior come from `PosteriorComputation`, `GraphNumerics`, `RetrievalRanking`, `CoreLibrary` and the concrete protocols, not the older approximations.
- Source inventory mappings are navigation and coverage evidence, not per-function Rust refinement theorems. Tests and examples are classified separately from production behavior.

Existing required laws remain authoritative where current Rust differs. The documented conformance work includes graph closure, paired document replacement, embedding reply association, candidate locking/freshness, capability handshake and temporary-file cleanup ownership. The original findings are retained in [FORMAL-REBUILD.md](FORMAL-REBUILD.md); implementation changes and verification are tracked in [RUST-CONFORMANCE.md](RUST-CONFORMANCE.md). The required laws remain unchanged.

## Verification

`python scripts/formal/check-coverage.py` verifies the exact tool/CLI inventory, referenced modules, complete root import closure, safety markers and all ten SQL body bindings. This structural audit does not replace Agda. The following timing and verification receipt describe the original nine-migration audit.

The persistent interactive root check passed with no errors or goals. The final batch Agda check passed with exit 0 in 53.657 seconds. Naming/deprecation warnings remain; there were no errors. Complete log: /tmp/mimir-formal-final-aggregate-4aAlpuul.log (exit status in .exit). This check reused completed interfaces; it is not a cold-rebuild claim.

The [verification receipt](FORMAL-BEHAVIOR-VERIFICATION.json) records commands, logs, coverage results, assumption boundaries and SHA-256 hashes of every checked formal source. Completion took 4.93 hours from the agreed start, before the eight-hour deadline.

Machine-readable maps: [FORMAL-BEHAVIOR-COVERAGE.json](FORMAL-BEHAVIOR-COVERAGE.json) and [FORMAL-INVENTORY.json](FORMAL-INVENTORY.json).

## PostgreSQL item-ID upgrade

The tenth migration preserves existing item IDs and ownership. It imports
missing owners from saved experiences and reviews, leaves established owners
unchanged even when old records conflict, and adds nullable local names with
per-experience uniqueness and a nonempty-name check. PostgreSQL supplies IDs
for future rows through its column default; its UUID guarantees are trusted.

`ItemOwnerBackfill` proves preservation of existing owners, retention of every
historical identity, repeatability, preservation of unrelated rows and rollback
behavior. `MigrationSchema` connects those rules to the migration's data change;
`MigrationScriptBinding` retains the exact loaded SQL body. Historical SQL
observation order is explicit: when an unreserved ID has conflicting old
declarations, the first observed declaration is retained.

### Incoming items and saved IDs

`LearningInput` separates an incoming item, whose ID may be absent, from a
saved item with its assigned ID. `LearningWire` uses these incoming types for
record/review requests and keeps IDs required when reading stored results.
Both the saved payload and its retry comparison retain the optional local key.

`LearningNormalization` connects the request to the saved key and ownership
tables. For example, a new item named `estimate-a` can omit its ID. The normalizer
uses the held learning transaction to ask PostgreSQL for the ID, retains that
returned ID in the item and key table, then resolves assessment `item_keys`
before the existing whole-payload validation. A supplied ID can reuse an
existing reservation; it cannot create a new item. Unknown names, a mismatched
ID/key or changed provenance refuse the operation. An acknowledged transaction
abort preserves the old keys and owners under the existing database contract;
an uncertain commit is not reported as a successful write.
Project deletion clears the keys of the deleted experiences while preserving
every unrelated experience's lookup.

`LearningOperations.Protocol.start` now includes that allocation phase in the
actual public operation. Its general `publicSuccessRequiresCommit` and scope
laws require an observed commit and the same held transaction. The named-request
retry laws derive each item from its saved key/owner observations, preserve IDs
and resolve to replay without another allocation or data write. PostgreSQL's
UUID generation remains an external operation; no uniqueness proof is added.

## Operational repair (2026-10-31)

That snapshot checked **643 safe modules**. `OperationalConfiguration`,
`ConfigurationUpgrade`, `OperationalLogRetention`, `OperationalDiagnostics`
and `OperationalLifecycle` cover required configuration compatibility, bounded
logs, public failure explanations and per-batch startup/retry. CLI coverage is
30 leaves, including `config check`, `config upgrade` and `judge diagnose`.
The quotation repair implements the existing `FaultWire`, `McpErrors` and
`JudgeErrorAdapter` contracts without weakening exact source matching.

See [operational verification](OPERATIONAL-REPAIR-VERIFICATION.json) and
[operating instructions](operations.md). The safe specification and observed
Rust/installed-service checks are separate evidence; no new postulates or
machine-checked Rust refinement theorem are claimed.
