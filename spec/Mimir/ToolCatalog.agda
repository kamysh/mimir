{-# OPTIONS --safe #-}
module Mimir.ToolCatalog where

open import Data.String using (String)

-- Public operation universe. Argument validation and operation semantics are
-- separate obligations; enumerating a tool does not prove its behavior.
data Tool : Set where
  insertBelief deleteBelief deleteProject deletePattern insertPattern : Tool
  recordSupport recordCause recordDefeat recordContradiction : Tool
  getBelief listBeliefs listPatterns getContradictions : Tool
  decayAll sweepExpiredDefeated queryRelevant : Tool
  addEvidence getEvidence propagateFrom queryIntervention : Tool
  loadDocument queryDocument clearDocument : Tool
  getLearningReview learningCapabilities getLessonAssessment : Tool
  lessonAssessmentHistory explainBelief recordExperience : Tool
  pendingExperiences reviewExperience getExperience experienceHistory : Tool
  queryLearningContext : Tool
  reserveOperation operationOutcome cancelOperation : Tool

-- Controls own their reservation/readback/cancellation protocol. A business
-- write instead requires a previously issued token alongside its arguments.
data Kind : Set where businessWrite readOnly operationControl : Kind

kind : Tool → Kind
kind insertBelief = businessWrite
kind deleteBelief = businessWrite
kind deleteProject = businessWrite
kind deletePattern = businessWrite
kind insertPattern = businessWrite
kind recordSupport = businessWrite
kind recordCause = businessWrite
kind recordDefeat = businessWrite
kind recordContradiction = businessWrite
kind getBelief = readOnly
kind listBeliefs = readOnly
kind listPatterns = readOnly
kind getContradictions = readOnly
kind decayAll = businessWrite
kind sweepExpiredDefeated = businessWrite
kind queryRelevant = readOnly
kind addEvidence = businessWrite
kind getEvidence = readOnly
kind propagateFrom = businessWrite
kind queryIntervention = readOnly
kind loadDocument = businessWrite
kind queryDocument = readOnly
kind clearDocument = businessWrite
kind getLearningReview = readOnly
kind learningCapabilities = readOnly
kind getLessonAssessment = readOnly
kind lessonAssessmentHistory = readOnly
kind explainBelief = readOnly
kind recordExperience = businessWrite
kind pendingExperiences = readOnly
kind reviewExperience = businessWrite
kind getExperience = readOnly
kind experienceHistory = readOnly
kind queryLearningContext = readOnly
kind reserveOperation = operationControl
kind operationOutcome = operationControl
kind cancelOperation = operationControl

wireName : Tool → String
wireName insertBelief = "insert_belief"
wireName deleteBelief = "delete_belief"
wireName deleteProject = "delete_project"
wireName deletePattern = "delete_pattern"
wireName insertPattern = "insert_pattern"
wireName recordSupport = "record_support"
wireName recordCause = "record_cause"
wireName recordDefeat = "record_defeat"
wireName recordContradiction = "record_contradiction"
wireName getBelief = "get_belief"
wireName listBeliefs = "list_beliefs"
wireName listPatterns = "list_patterns"
wireName getContradictions = "get_contradictions"
wireName decayAll = "decay_all"
wireName sweepExpiredDefeated = "sweep_expired_defeated"
wireName queryRelevant = "query_relevant"
wireName addEvidence = "add_evidence"
wireName getEvidence = "get_evidence"
wireName propagateFrom = "propagate_from"
wireName queryIntervention = "query_intervention"
wireName loadDocument = "load_document"
wireName queryDocument = "query_document"
wireName clearDocument = "clear_document"
wireName getLearningReview = "get_learning_review"
wireName learningCapabilities = "learning_capabilities"
wireName getLessonAssessment = "get_lesson_assessment"
wireName lessonAssessmentHistory = "lesson_assessment_history"
wireName explainBelief = "explain_belief"
wireName recordExperience = "record_experience"
wireName pendingExperiences = "pending_experiences"
wireName reviewExperience = "review_experience"
wireName getExperience = "get_experience"
wireName experienceHistory = "experience_history"
wireName queryLearningContext = "query_learning_context"
wireName reserveOperation = "reserve_operation"
wireName operationOutcome = "operation_outcome"
wireName cancelOperation = "cancel_operation"
