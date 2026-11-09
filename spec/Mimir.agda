{-# OPTIONS --safe #-}
-- Top-level re-export module.
-- Import this for access to the full Mimir spec in one open.
-- Import individual submodules for targeted access:
--   Mimir.Types     — core data types (Prob, NodeId, Belief, Pattern, …)
--   Mimir.Inference — inference engine (attenuate, decay, boost, proofs)
--   Mimir.Graph     — graph operations (edges, BFS, sort, MCP semantics)
--   Mimir.Beta      — Phase 3: beliefs as Beta(α,β) (mean monotonicity, idempotence)
--   Mimir.Session   — session-scoped project side channel for hook injection (#9)
module Mimir where

import Mimir.ReleaseSource
import Mimir.JudgeRevision
import Mimir.JudgeWorkflow
import Mimir.JudgeConfiguration
import Mimir.JudgeProcess
import Mimir.JudgeJSON
import Mimir.JudgePrompt
import Mimir.JudgeHarnessAdapter
import Mimir.JudgeAPIAdapter
import Mimir.JudgeBackendComposition
import Mimir.NotificationConfigurationWire

import Mimir.ConfigurationProtocol
import Mimir.EmbeddingLifecycle
import Mimir.MigrationSchema
import Mimir.CLI
import Mimir.HookProtocol
import Mimir.StorageSemantics
import Mimir.ConnectionProtocol
import Mimir.ServiceStartup
import Mimir.McpRuntimeComposition
import Mimir.LearningStateWire
import Mimir.JudgeScopedTools

import Mimir.JudgeBatchConfirmation
import Mimir.LearningPublication
import Mimir.ReviewPlan
import Mimir.ReviewJournal
import Mimir.DatabaseTransaction
import Mimir.DatabaseReadCommitted
import Mimir.LearningTransaction
import Mimir.LearningTransactionReceipt
import Mimir.LearningInput
import Mimir.LearningNormalization
import Mimir.ReviewTransaction
import Mimir.ReviewSerialization
import Mimir.LearningTransactionDatabase
import Mimir.ReviewCompetition
import Mimir.NativeLockOrder
import Mimir.DatabaseAdvisoryLock
import Mimir.AssessmentSelection

import Mimir.BitLogic

import Mimir.SignedMachine

import Mimir.Effects
import Mimir.Recovery
import Mimir.RecoverableStoreStep
import Mimir.RegisteredStoreAdmission
import Mimir.BeliefDeletionRecovery
import Mimir.GroundingRecovery
import Mimir.AtomicFile
import Mimir.CharacterRules
import Mimir.OAuthCache
import Mimir.SMTPAuth
import Mimir.CompleteBytes
import Mimir.BoundedBytes
import Mimir.OAuthHTTP
import Mimir.TextOrder
import Mimir.DigestDelivery
import Mimir.NotificationSchema
import Mimir.TrimLaws
import Mimir.TextFields
import Mimir.EmailAddress
import Mimir.WhitespaceWords
import Mimir.NotificationConfig
import Mimir.UnsignedWire
import Mimir.OAuthWire
import Mimir.Radix
import Mimir.Bits
import Mimir.NotificationDelivery

import Mimir.Connection
import Mimir.Startup

open import Mimir.Types     public
open import Mimir.Inference public
open import Mimir.Graph     public
open import Mimir.Evidence  public
open import Mimir.Beta      public
open import Mimir.Session   public

open import Mimir.Learning  public

-- Namespaced contracts avoid collisions with the existing public graph laws.
import Mimir.LearningContracts
import Mimir.Judge
import Mimir.Assessment
import Mimir.SourceText
import Mimir.SourceProtocol
import Mimir.ToolCatalog
import Mimir.Password
import Mimir.ConfigurationIO
import Mimir.Validation
import Mimir.Text
import Mimir.SourceSchema
import Mimir.SourceReview
import Mimir.Binary64
import Mimir.NumericValidation
import Mimir.LearningSchema
import Mimir.CommitProtocol
import Mimir.JudgeReview
import Mimir.Framing
import Mimir.RpcReply
import Mimir.Migrations
import Mimir.DocumentStore
import Mimir.Markdown
import Mimir.EmbeddingBatch
import Mimir.Unsigned
import Mimir.ConfigurationValues
import Mimir.ConfigurationInput
import Mimir.ConfigurationPath
import Mimir.TLS
import Mimir.Collections
import Mimir.LearningCandidates
import Mimir.ReviewSchema
import Mimir.ExperienceSchema
import Mimir.OptionalTraversal
import Mimir.ReviewResolution
import Mimir.Retention
import Mimir.LearningCorrections
import Mimir.CandidateRegistry
import Mimir.CandidateBatch
import Mimir.CandidateReview
import Mimir.CandidateReplay
import Mimir.CandidateGraph
import Mimir.CandidatePublication
import Mimir.ReviewPreparation
import Mimir.ItemOwners
import Mimir.ItemAllocation
import Mimir.JudgeAccounting
import Mimir.ReviewObservation
import Mimir.SemanticKey
import Mimir.LearningKeys
import Mimir.RevisionBounds
import Mimir.LearningRevision
import Mimir.LearningTargets
import Mimir.JsonObjects
import Mimir.StructuredValue
import Mimir.RecordDecoding
import Mimir.SourceWire
import Mimir.ReviewAdmission
import Mimir.CandidateWire
import Mimir.JudgeAcknowledgement
import Mimir.JudgeReceipt
import Mimir.ProviderQueue
import Mimir.JudgeTools
import Mimir.JudgeQueueAdapter
import Mimir.FaultWire
import Mimir.McpErrors
import Mimir.JudgeErrorAdapter
import Mimir.BatchReport
import Mimir.DeferredReviews
import Mimir.PendingSelection
import Mimir.ExperiencePending
import Mimir.CandidateDeferral
import Mimir.NotificationIncident
import Mimir.Saturating
import Mimir.ReadLine
import Mimir.McpEnvelope
import Mimir.McpInput
import Mimir.McpExchange
import Mimir.McpRuntime
import Mimir.StablePartition
import Mimir.PriorityFields
import Mimir.AgentFieldOrder
import Mimir.MigrationFinalization
import Mimir.MigrationDriver
import Mimir.EffectRestriction
import Mimir.MigrationLedgerWrite
import Mimir.EffectExpansion
import Mimir.EffectDecomposition
import Mimir.MigrationComposition
import Mimir.MigrationValidation
import Mimir.ExactBytes
import Mimir.FiniteTable
import Mimir.MigrationLedger
import Mimir.MigrationRows
import Mimir.MigrationHistory
import Mimir.MigrationBootstrap
import Mimir.MigrationImport
import Mimir.MigrationImportValues
import Mimir.MigrationRuntime
import Mimir.JudgeControllerAccounting
import Mimir.JudgeTraceBarrier
import Mimir.SelectiveTraversal
import Mimir.ProviderResponse
import Mimir.ProviderCollection
import Mimir.ProviderReplay
import Mimir.ProviderArguments
import Mimir.ProviderQueueAdmission
import Mimir.LearningCapabilities
import Mimir.McpToolAdvertisement
import Mimir.JudgeToolCatalogue
import Mimir.JudgeHandshake
import Mimir.McpClientWire
import Mimir.McpClientRequest
import Mimir.McpClientLine
import Mimir.McpClientLineLaws
import Mimir.McpErrorWire
import Mimir.McpErrorDelivery
import Mimir.WriteAllFlush
import Mimir.McpSendBytes
import Mimir.DiagnosticText
import Mimir.SourceFailure
import Mimir.JudgeStateRecords
import Mimir.JudgeConfirmationLedger
import Mimir.JudgeIncident
import Mimir.JudgeIncidentEvidence
import Mimir.UnsignedMachine
import Mimir.FirstListMatch
import Mimir.JudgeTraceSelection
import Mimir.JudgeTraceStart
import Mimir.JudgeTraceMutation
import Mimir.UUIDGroups
import Mimir.UUIDSchema
import Mimir.JudgeStateWire
import Mimir.SerdeSequence
import Mimir.SerdeStruct
import Mimir.JudgeStatePrimitives
import Mimir.JudgeStateDecode
import Mimir.SerdeEmission
import Mimir.JudgeStateBounds
import Mimir.SerdeEmissionBuilders
import Mimir.JudgeStateRoundTrip
import Mimir.SerdeObtained
import Mimir.JudgeStateFieldLaws
import Mimir.BitMaskClear
import Mimir.UnixMetadata
import Mimir.UnixMetadataLaws
import Mimir.JudgeFilesystem
import Mimir.JudgeDirectory
import Mimir.EffectsComposition
import Mimir.JudgeLock
import Mimir.JudgeRead
import Mimir.JudgeWrite
import Mimir.UnixPath
import Mimir.UnixPathParts
import Mimir.UnixPathLaws
import Mimir.JudgeStatePath
import Mimir.UnixPathParent
import Mimir.ASCIIPath
import Mimir.JudgePersistence
import Mimir.EffectsHandling
import Mimir.JudgeWriteReceipt
import Mimir.JudgeFilesystemDisplay

import Mimir.UUIDV4
import Mimir.JudgeNamedWrite
import Mimir.JudgeRecordWrite
import Mimir.JudgeStateDocument
import Mimir.EffectMap


















































import Mimir.McpClientTransport
import Mimir.McpTransportEffect



import Mimir.McpClientLineDiagnostic


import Mimir.FloatValue
import Mimir.StandardLibrary

import Mimir.CandidateGraphUniqueness
import Mimir.ItemOwnerBatch

import Mimir.ReviewLedger

import Mimir.ReviewPreparationPublication
import Mimir.ReviewPlanning
import Mimir.AssessmentWrites
import Mimir.AssessmentHistory

import Mimir.ReviewEdges
import Mimir.ReviewRecomputeTraversal
import Mimir.ApplicationFloat
import Mimir.AssessmentScores
import Mimir.AssessmentEvaluation
import Mimir.AssessmentRead
import Mimir.ExperienceRead
import Mimir.PosteriorComputation
import Mimir.EvidenceValidity
import Mimir.LearningRecompute
import Mimir.ReviewNumericalPublication
import Mimir.LearningStore
import Mimir.ExperienceRecord
import Mimir.ReviewRecord
import Mimir.LearningOperations
import Mimir.LearningHistory
import Mimir.PatternOutcomes
import Mimir.IndependentProvenance
import Mimir.CandidateProvenance
import Mimir.BeliefExplanation
import Mimir.LearningAssessmentQueries
import Mimir.LearningQueryProtocol

import Mimir.RetrievalRanking
import Mimir.RetrievalProtocol
import Mimir.LearningContext
import Mimir.GraphNumerics
import Mimir.GraphRecords
import Mimir.ApplicationStore
import Mimir.GraphDeletion
import Mimir.InferenceProtocol
import Mimir.GraphWrites
import Mimir.GraphPaths
import Mimir.RetrievalReadContract
import Mimir.LearningContextProtocol
import Mimir.JudgeHost
import Mimir.JudgeFinalization
import Mimir.JudgeSelection
import Mimir.JudgeRevisionPolicy
import Mimir.JudgeBatchReadback
import Mimir.DocumentPublication
import Mimir.GroundingPublication
import Mimir.GroundingProtocol
import Mimir.DocumentLoading
import Mimir.EvidenceRead
import Mimir.DocumentQuery
import Mimir.BeliefEmbedding
import Mimir.EmbeddingBackend
import Mimir.ProjectDeletion
import Mimir.GraphReadProtocol
import Mimir.GraphMutationProtocol
import Mimir.PublicInput
import Mimir.LearningWire
import Mimir.PublicRequest
import Mimir.ApplicationProtocol
import Mimir.PublicEncoding
import Mimir.ApplicationOutput
import Mimir.McpToolExecution
import Mimir.McpApplicationComposition
import Mimir.ConfigurationSchema

import Mimir.JudgeServiceBinding

import Mimir.JudgeWorkflowComposition

import Mimir.McpServiceProcess
import Mimir.JudgeConfigurationComposition

import Mimir.JudgeStatusProtocol

import Mimir.JudgeHostProtocol

import Mimir.StorageReadBinding

import Mimir.MigrationScriptBinding

import Mimir.JudgeStateMap

import Mimir.JudgePersistenceComposition

import Mimir.LearningHistoryWire

import Mimir.LearningQueryBinding

import Mimir.NotificationRuntime

import Mimir.NotificationWire

import Mimir.OAuthComposition

import Mimir.OAuthResponseBinding

import Mimir.SMTPProtocol

import Mimir.NotificationStorage

import Mimir.JudgeStateOperations

import Mimir.JudgeNotification

import Mimir.JudgeFinalizationComposition

import Mimir.JudgeMcpLifecycle

import Mimir.JudgeBatchServiceBinding

import Mimir.JudgeDigest

import Mimir.JudgeHandshakeBinding

import Mimir.EmbeddingService

import Mimir.OAuthRefreshRaw

import Mimir.JudgeDigestSnapshot
import Mimir.LocalCalendar

import Mimir.JudgeClientStartup

import Mimir.GroundingStorageBinding

import Mimir.InferenceStorageBinding

import Mimir.NotificationCodec

import Mimir.NotificationFileBinding

import Mimir.NotificationMail

import Mimir.NotificationComposition

import Mimir.ServiceConnection

import Mimir.CLIServiceBinding

import Mimir.JudgeDigestComposition

import Mimir.CLIReembed

import Mimir.BeliefEmbeddingStorage
import Mimir.StoreRows
import Mimir.AgeQueryProtocol
import Mimir.CoreLibrary

import Mimir.OperationalConfiguration
import Mimir.OperationalLogRetention
import Mimir.OperationalLogProtocol
import Mimir.ConfigurationUpgrade
import Mimir.OperationalDiagnostics
import Mimir.OperationalLifecycle

import Mimir.OptionalLimit

import Mimir.JudgeSignal
import Mimir.JudgeOwnedWork
import Mimir.JudgeSignalBinding
import Mimir.JudgeCommandExecution

import Mimir.PreparedRetrieval
import Mimir.TraversalCompleteness
