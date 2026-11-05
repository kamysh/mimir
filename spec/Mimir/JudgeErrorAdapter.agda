{-# OPTIONS --safe #-}
module Mimir.JudgeErrorAdapter where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Validation using (Fault)
open import Mimir.ReviewObservation using (Pin)
import Mimir.McpErrors as Mcp
import Mimir.JudgeReview as Review

module Adapter (Payload : Set) (selected : Pin) where
  module C = Review.Controller Payload selected

  data Dispatch : Set where
    ordinary : C.ToolReply → Dispatch
    candidateConflict candidateReference : Fault → Dispatch

  route : Mcp.Classification → Dispatch
  route (Mcp.rejected (Mcp.refusal Mcp.invalidInput detail)) = ordinary (C.refused detail)
  route (Mcp.rejected (Mcp.refusal Mcp.candidateConflict detail)) = candidateConflict detail
  route (Mcp.rejected (Mcp.refusal Mcp.undeclaredCandidate detail)) = candidateReference detail
  route (Mcp.unclassified failure) = ordinary (C.indeterminate failure)

  exactFaultReachesController : ∀ detail →
    route (Mcp.classify (Mcp.encode (Mcp.refusal Mcp.invalidInput detail))) ≡ ordinary (C.refused detail)
  exactFaultReachesController detail rewrite Mcp.roundTrip (Mcp.refusal Mcp.invalidInput detail) = refl

  unknownFailureCannotClaimInvalidArguments : ∀ failure →
    route (Mcp.unclassified failure) ≡ ordinary (C.indeterminate failure)
  unknownFailureCannotClaimInvalidArguments failure = refl

  candidateFailureRemainsDistinct : ∀ detail →
    route (Mcp.classify (Mcp.encode (Mcp.refusal Mcp.candidateConflict detail))) ≡ candidateConflict detail
  candidateFailureRemainsDistinct detail rewrite Mcp.roundTrip (Mcp.refusal Mcp.candidateConflict detail) = refl
