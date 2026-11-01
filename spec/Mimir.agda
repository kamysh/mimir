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
import Mimir.ReviewTransaction
import Mimir.ReviewSerialization
import Mimir.DatabaseAdvisoryLock
import Mimir.AssessmentSelection

import Mimir.ParserSafety
import Mimir.MigrationParserSafety
import Mimir.UpperBoundary
import Mimir.UnicodeSkipSearch
import Mimir.RustUnicodeData
import Mimir.RustUnicode
import Mimir.UnicodeSkipBounds
import Mimir.RustUnicodeBounds
import Mimir.MigrationKeySyntax
import Mimir.ModularWord
import Mimir.BitLogic
import Mimir.WordAddition
import Mimir.WordEncoding
import Mimir.WordShifts
import Mimir.SHA256Round
import Mimir.SHA256Schedule
import Mimir.SHA256Compression
import Mimir.SHA256Constants
import Mimir.SHA256Core
import Mimir.VectorChunks
import Mimir.WordBytes
import Mimir.FixedBlocks
import Mimir.VectorFill
import Mimir.SHA256Padding
import Mimir.SHA256Hash
import Mimir.TextPredicatePreservation
import Mimir.UnicodeChecksum
import Mimir.UnicodeParser
import Mimir.MigrationChecksumSyntax
import Mimir.UnicodeParserSafety
import Mimir.MigrationChecksumSafety
import Mimir.WinnowPosition
import Mimir.WinnowLines
import Mimir.UnicodeCursorBytes
import Mimir.MigrationFileParsing
import Mimir.MigrationLoadContract
import Mimir.MigrationFileRuntime

import Mimir.SignedMachine
import Mimir.SequenceCursor
import Mimir.SerdeNumeric
import Mimir.ByteCursorTransport
import Mimir.SerdeNumericWire
import Mimir.FinalizingCursor
import Mimir.JsonControls
import Mimir.CursorProgress
import Mimir.SerdeNumericProgress
import Mimir.JsonFlow
import Mimir.JsonCollection
import Mimir.JsonAtoms
import Mimir.JsonTreeParser
import Mimir.JsonTree
import Mimir.JsonTreeBounds
import Mimir.ByteKeyOrder
import Mimir.OrderedObject
import Mimir.JsonStoredValue
import Mimir.JsonCompletion
import Mimir.JsonDecode
import Mimir.JsonPosition
import Mimir.NatDecimal
import Mimir.JsonErrorDisplay

import Mimir.Effects
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
import Mimir.UTF8Byte
import Mimir.UTF8Packet
import Mimir.UTF8Text
import Mimir.UnicodeScalar
import Mimir.UnicodeText
import Mimir.UTF16Escape
import Mimir.HexEscape
import Mimir.JsonEscape
import Mimir.ByteCursor
import Mimir.JsonEscapeParser
import Mimir.JsonString
import Mimir.JsonStringParser
import Mimir.JsonLiteral
import Mimir.JsonStringWriter
import Mimir.ByteText
import Mimir.BytePart
import Mimir.JsonNumberWire
import Mimir.JsonNumberSuffix
import Mimir.JsonWhitespace
import Mimir.JsonSurface
import Mimir.NotificationDelivery

import Mimir.Connection
import Mimir.Startup

open import Mimir.Types     public
open import Mimir.Inference public
open import Mimir.Graph     public
open import Mimir.Documents public
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
import Mimir.JudgeAccounting
import Mimir.ReviewObservation
import Mimir.SemanticKey
import Mimir.LearningKeys
import Mimir.RevisionBounds
import Mimir.LearningRevision
import Mimir.LearningTargets
import Mimir.DecimalLexer
import Mimir.ParsedPart
import Mimir.JsonNumber
import Mimir.JsonNumberCompleteness
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
import Mimir.CandidateDeferral
import Mimir.NotificationIncident
import Mimir.Saturating
import Mimir.JsonNumericValue
import Mimir.ReadLine
import Mimir.McpEnvelope
import Mimir.ScalarText
import Mimir.McpInput
import Mimir.McpExchange
import Mimir.McpRuntime
import Mimir.FiniteBooleanRange
import Mimir.ScalarCharacter
import Mimir.DecodedText
import Mimir.JsonSchemaValue
import Mimir.UTF8ScalarIdentity
import Mimir.DecodedKey
import Mimir.JsonSchemaLookup
import Mimir.SchemaDocument
import Mimir.StablePartition
import Mimir.PriorityFields
import Mimir.JsonIntegerWriter
import Mimir.AgentFieldOrder
import Mimir.DecodedTextByteLength
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
import Mimir.ReadySelection
import Mimir.TopologicalSchedule
import Mimir.DependencyCount
import Mimir.MigrationDependencies
import Mimir.MigrationImport
import Mimir.LowerHex
import Mimir.MigrationImportValues
import Mimir.MigrationRuntime
import Mimir.MigrationQuoted
import Mimir.MigrationHeader
import Mimir.MigrationImplicit
import Mimir.SubstringScan
import Mimir.WhitespaceCut
import Mimir.MigrationSlices
import Mimir.BacktrackingParser
import Mimir.MigrationSyntax
import Mimir.ScalarCharacterCheck
import Mimir.ScalarCharacter.Plane0
import Mimir.ScalarCharacter.Plane1
import Mimir.ScalarCharacter.Plane2
import Mimir.ScalarCharacter.Plane3
import Mimir.ScalarCharacter.Plane4
import Mimir.ScalarCharacter.Plane5
import Mimir.ScalarCharacter.Plane6
import Mimir.ScalarCharacter.Plane7
import Mimir.ScalarCharacter.Plane8
import Mimir.ScalarCharacter.Plane9
import Mimir.ScalarCharacter.Plane10
import Mimir.ScalarCharacter.Plane11
import Mimir.ScalarCharacter.Plane12
import Mimir.ScalarCharacter.Plane13
import Mimir.ScalarCharacter.Plane14
import Mimir.ScalarCharacter.Plane15
import Mimir.ScalarCharacter.Plane16
import Mimir.JudgeControllerAccounting
import Mimir.JudgeTraceBarrier
import Mimir.SelectiveTraversal
import Mimir.ProviderResponse
import Mimir.ProviderCollection
import Mimir.ProviderReplay
import Mimir.SerdeNumericOrdinary
import Mimir.JsonOrdinary
import Mimir.JsonReleaseDocument
import Mimir.JsonDiagnosticCode
import Mimir.JsonControlDiagnostics
import Mimir.JsonDiagnostics
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
import Mimir.UTF8LossyTail
import Mimir.UTF8LossyGroup
import Mimir.UTF8LossyBytes
import Mimir.UTF8ByteRanges
import Mimir.UTF8ByteDecode
import Mimir.UTF8PacketValue
import Mimir.UTF8CanonicalBounds
import Mimir.UTF8LossyPayload
import Mimir.UTF8LossyConditions
import Mimir.UTF8LossyCanonical
import Mimir.UTF8LossyValid
import Mimir.UTF8LossyText
import Mimir.NatSeparation
import Mimir.UTF8CanonicalNecessity
import Mimir.UTF8LossyGroupComplete
import Mimir.UTF8LossyAdmission
import Mimir.UTF8LossyPacket
import Mimir.UTF8LossyIdentity
import Mimir.SourceWindow
import Mimir.SourceLineOffset
import Mimir.SourceFailure
import Mimir.UTF8LossyChunks
import Mimir.UTF8ChunkValidity
import Mimir.JudgeStateRecords
import Mimir.JudgeConfirmationLedger
import Mimir.JudgeIncident
import Mimir.JudgeIncidentEvidence
import Mimir.UnsignedMachine
import Mimir.JudgeTraceEvent
import Mimir.LastElement
import Mimir.JudgeTraceTrim
import Mimir.FirstListMatch
import Mimir.JudgeTraceSelection
import Mimir.JudgeTraceRetention
import Mimir.JudgeTraceStart
import Mimir.JudgeTraceMutation
import Mimir.ByteHex
import Mimir.UUIDHexClassifier
import Mimir.HexBytes
import Mimir.UUIDGroups
import Mimir.UUIDHyphenated
import Mimir.UUIDLowerFormatting
import Mimir.UUIDParse
import Mimir.UUIDHyphenatedGrammar
import Mimir.UUIDParseGrammar
import Mimir.UUIDParseComplete
import Mimir.UUIDAcceptance
import Mimir.ASCIIText
import Mimir.UUIDJson
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
import Mimir.JudgeStateReadBounds
import Mimir.JsonTextWriter
import Mimir.JsonCompactRecords
import Mimir.JudgeStateText
import Mimir.JsonRecordSupport
import Mimir.JudgeStateSerialize
import Mimir.JsonCompactIdentity
import Mimir.JudgeTraceConcrete
import Mimir.EffectsInterpret
import Mimir.JudgeTrimConcrete
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
import Mimir.UnixPathAncestry
import Mimir.ASCIIPath
import Mimir.JudgePersistence
import Mimir.NativeWriteAll
import Mimir.NativeTake
import Mimir.EffectsHandling
import Mimir.JudgeWriteReceipt
import Mimir.JudgeFilesystemDisplay

import Mimir.BitOverwrite
import Mimir.UUIDVersionBits
import Mimir.UUIDV4
import Mimir.JudgeNamedWrite
import Mimir.JudgeRecordWrite
import Mimir.JsonIgnoredEscape
import Mimir.JsonIgnoredString
import Mimir.JsonIgnoredNumber
import Mimir.JsonIgnoredStep
import Mimir.JsonIgnoredRun
import Mimir.JsonIgnoredNumberComplete
import Mimir.JsonIgnoredNumberWire
import Mimir.SerdeFlow
import Mimir.SerdeSlots
import Mimir.SerdeMember
import Mimir.SerdeLoop
import Mimir.SerdeMap
import Mimir.SerdePositional
import Mimir.SerdeSuccess
import Mimir.SerdeScalar
import Mimir.SerdeContainer
import Mimir.SerdeRecord
import Mimir.SerdeVector
import Mimir.SerdeOption
import Mimir.JudgeStateAtoms
import Mimir.JudgeStateRaw
import Mimir.SerdeDocument
import Mimir.JudgeStateDocument
import Mimir.EffectMap
import Mimir.JudgeParsedRead
import Mimir.JudgeRecordRead
import Mimir.SerdeSlotInvariant
import Mimir.SerdeMemberInvariant
import Mimir.SerdeLoopInvariant
import Mimir.SerdeMapInvariant
import Mimir.SerdePositionalInvariant
import Mimir.SerdeParserInvariant
import Mimir.SerdeRecordInvariant
import Mimir.SerdeVectorInvariant
import Mimir.SerdeOptionInvariant

import Mimir.SerdeSuccessTransfer
import Mimir.JudgeRawInvariant
import Mimir.JudgeRawLeafBounds
import Mimir.JudgeRawCompositeBounds
import Mimir.SerdeDocumentInvariant
import Mimir.JudgeDocumentBounds
import Mimir.JudgeRecordBounds

import Mimir.SerdeValidateInvariant
import Mimir.SerdeScalarUnicode
import Mimir.JudgeRawText
import Mimir.JudgeRecordText

import Mimir.SerdeReadBack
import Mimir.JudgeTextReadBack
import Mimir.JudgeUUIDReadBack

import Mimir.SequenceReadBack
import Mimir.SerdeIntegerReadBack
import Mimir.SerdeUnsignedReadBack
import Mimir.ByteReadBack
import Mimir.SerdeUnsignedWireReadBack
import Mimir.SerdeReadBackComposition
import Mimir.SerdeNumberStart
import Mimir.SerdeNumberReadBack
import Mimir.JudgeUnsignedReadBack
import Mimir.SignedMagnitude
import Mimir.SignedIntegerBounds
import Mimir.SerdeIntegerAccumulation
import Mimir.SerdeNegativeReadBack
import Mimir.SerdeNegativeWireReadBack
import Mimir.JudgeSignedReadBack

import Mimir.SerdeOptionReadBack

import Mimir.SerdeLoopReadBack

import Mimir.SerdeVectorReadBack

import Mimir.JsonArrayReadBack

import Mimir.JudgeUUIDVectorReadBack

import Mimir.SerdeMemberReadBack

import Mimir.SerdeMapReadBack

import Mimir.JsonObjectReadBack

import Mimir.SerdeObjectReadBack

import Mimir.JudgeDeferredReadBack

import Mimir.JudgeConfirmedReadBack

import Mimir.JudgeSourceReadBack

import Mimir.JudgeDiagnosticReadBack

import Mimir.SerdeRawEmission

import Mimir.SerdeRawEmissionBuilders

import Mimir.SerdeOptionCodecReadBack

import Mimir.JudgeEventReadBack

import Mimir.SerdeValidatedVectorReadBack

import Mimir.SerdeObjectVectorReadBack

import Mimir.JudgeTraceReadBack

import Mimir.JudgeDiagnosticsReadBack

import Mimir.JudgeReportReadBack

import Mimir.JudgeIncidentReadBack

import Mimir.SerdeDocumentReadBack

import Mimir.JudgeStateDocumentReadBack

import Mimir.JudgeParsedReadBack

import Mimir.JudgeRecordReadBack

import Mimir.SerdeUnknownMemberReadBack

import Mimir.JsonIgnoredReadBack

import Mimir.JsonIgnoredNumberReadBack

import Mimir.JsonIgnoredNumberSyntax

import Mimir.JsonIgnoredNumberWireReadBack

import Mimir.JsonIgnoredPath

import Mimir.JsonIgnoredScalarPath

import Mimir.JsonIgnoredContainerPath

import Mimir.JsonIgnoredValueSyntax

import Mimir.JsonIgnoredValueReadBack

import Mimir.JsonIgnoredWhitespacePath

import Mimir.JsonIgnoredKeyWhitespace

import Mimir.JsonIgnoredSpacedSyntax

import Mimir.JsonIgnoredSpacedReadBack

import Mimir.JsonIgnoredFailure

import Mimir.SerdeSpacedMemberReadBack

import Mimir.SerdeFailure

import Mimir.SerdeMemberFailure

import Mimir.McpClientTransport
import Mimir.McpTransportEffect

import Mimir.EffectsPrefixComposition

import Mimir.EffectsHandlingPrefix

import Mimir.McpClientLineDiagnostic


import Mimir.FloatValue
import Mimir.FloatConversion
import Mimir.NumericTokens

import Mimir.CandidateGraphUniqueness
import Mimir.ItemOwnerBatch

import Mimir.ReviewLedger

import Mimir.ReviewPreparationPublication
import Mimir.ReviewPlanning
import Mimir.AssessmentWrites
import Mimir.AssessmentHistory

import Mimir.JudgeReportReferenceReadBack
import Mimir.ReviewEdges
import Mimir.ReviewRecomputeTraversal
import Mimir.ApplicationFloat
import Mimir.AssessmentScores
import Mimir.AssessmentEvaluation
import Mimir.AssessmentRead
import Mimir.ExperienceRead
import Mimir.PosteriorComputation
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
import Mimir.ConfigurationUpgrade
import Mimir.OperationalDiagnostics
import Mimir.OperationalLifecycle

import Mimir.OptionalLimit

import Mimir.JudgeSignal
