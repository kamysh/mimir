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

import Mimir.JudgeRevision
import Mimir.JudgeWorkflow
import Mimir.JudgeConfiguration
import Mimir.JudgeJSON
import Mimir.JudgeBackendComposition
import Mimir.NotificationConfigurationWire

import Mimir.ConfigurationProtocol
import Mimir.MigrationSchema
import Mimir.CLI
import Mimir.HookProtocol
import Mimir.ConnectionProtocol
import Mimir.ServiceStartup
import Mimir.McpRuntimeComposition
import Mimir.LearningStateWire
import Mimir.JudgeScopedTools

import Mimir.LearningPublication
import Mimir.ReviewPlan
import Mimir.ReviewJournal
import Mimir.DatabaseTransaction
import Mimir.LearningTransaction
import Mimir.LearningTransactionReceipt
import Mimir.LearningInput
import Mimir.LearningNormalization
import Mimir.ReviewTransaction
import Mimir.DatabaseAdvisoryLock
import Mimir.AssessmentSelection

import Mimir.BitLogic

import Mimir.SignedMachine

import Mimir.Effects
import Mimir.Recovery
import Mimir.CharacterRules
import Mimir.NotificationSchema
import Mimir.TextFields
import Mimir.EmailAddress
import Mimir.WhitespaceWords
import Mimir.NotificationConfig
import Mimir.Radix
import Mimir.Bits

import Mimir.Connection

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
import Mimir.ReviewObservation
import Mimir.SemanticKey
import Mimir.LearningKeys
import Mimir.RevisionBounds
import Mimir.LearningTargets
import Mimir.JsonObjects
import Mimir.StructuredValue
import Mimir.RecordDecoding
import Mimir.SourceWire
import Mimir.ReviewAdmission
import Mimir.CandidateWire
import Mimir.JudgeAcknowledgement
import Mimir.JudgeTools
import Mimir.FaultWire
import Mimir.McpErrors
import Mimir.BatchReport
import Mimir.DeferredReviews
import Mimir.PendingSelection
import Mimir.CandidateDeferral
import Mimir.NotificationIncident
import Mimir.ReadLine
import Mimir.McpEnvelope
import Mimir.McpInput
import Mimir.McpExchange
import Mimir.McpRuntime
import Mimir.MigrationFinalization
import Mimir.MigrationDriver
import Mimir.EffectRestriction
import Mimir.MigrationLedgerWrite
import Mimir.EffectExpansion
import Mimir.EffectDecomposition
import Mimir.MigrationValidation
import Mimir.ExactBytes
import Mimir.FiniteTable
import Mimir.MigrationLedger
import Mimir.MigrationRows
import Mimir.MigrationHistory
import Mimir.MigrationBootstrap
import Mimir.MigrationImport
import Mimir.MigrationImportValues
import Mimir.MigrationScriptBinding
import Mimir.MigrationRuntime
import Mimir.LearningCapabilities
import Mimir.McpToolAdvertisement
import Mimir.JudgeToolCatalogue
import Mimir.JudgeHandshake
import Mimir.McpClientWire
import Mimir.McpClientRequest
import Mimir.McpClientLine
import Mimir.McpErrorWire
import Mimir.WriteAllFlush
import Mimir.McpSendBytes
import Mimir.SourceFailure
import Mimir.JudgeStateRecords
import Mimir.JudgeConfirmationLedger
import Mimir.JudgeIncident
import Mimir.JudgeIncidentEvidence
import Mimir.UnsignedMachine
import Mimir.UUIDGroups
import Mimir.UUIDSchema
import Mimir.SerdeSequence
import Mimir.BitMaskClear
import Mimir.UnixMetadata
import Mimir.JudgeFilesystem
import Mimir.JudgeDirectory
import Mimir.EffectsComposition
import Mimir.JudgeLock
import Mimir.JudgeRead
import Mimir.UnixPath
import Mimir.UnixPathParts
import Mimir.UnixPathLaws
import Mimir.JudgeStatePath
import Mimir.UnixPathParent
import Mimir.ASCIIPath
import Mimir.JudgePersistence
import Mimir.EffectsHandling

import Mimir.EffectMap


















































import Mimir.McpClientTransport
import Mimir.McpTransportEffect





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
import Mimir.LearningContextProtocol
import Mimir.JudgeHost
import Mimir.JudgeFinalization
import Mimir.JudgeSelection
import Mimir.JudgeRevisionPolicy
import Mimir.JudgeBatchReadback
import Mimir.DocumentPublication
import Mimir.GroundingPublication
import Mimir.DocumentLoading
import Mimir.EvidenceRead
import Mimir.DocumentQuery
import Mimir.BeliefEmbedding
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

import Mimir.JudgeConfigurationComposition

import Mimir.JudgeStatusProtocol

import Mimir.JudgeHostProtocol





import Mimir.LearningHistoryWire








import Mimir.JudgeStateOperations


import Mimir.JudgeFinalizationComposition

import Mimir.JudgeMcpLifecycle

import Mimir.JudgeBatchServiceBinding


import Mimir.JudgeHandshakeBinding




import Mimir.JudgeClientStartup







import Mimir.ServiceConnection

import Mimir.CLIServiceBinding




import Mimir.OperationalConfiguration
import Mimir.OperationalLogRetention
import Mimir.OperationalLogSteps
import Mimir.OperationalLogProtocol
import Mimir.OperationalLifecycle

import Mimir.OptionalLimit
