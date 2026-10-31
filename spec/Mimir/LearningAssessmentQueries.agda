{-# OPTIONS --safe #-}
-- Bind assessment reads to actual stored review timestamps and graph targets.
module Mimir.LearningAssessmentQueries where

open import Data.List using (map)
open import Data.Nat using (ℕ)
import Mimir.LearningStore as Store
import Mimir.ReviewPreparationPublication as Publication
import Mimir.AssessmentRead as Read
import Mimir.AssessmentSelection as Selection
import Mimir.LearningRecompute as Recompute

view : Store.World → Read.World
view w = Read.world (Publication.World.ledger (Store.World.publication w))
  (Publication.World.assessments (Store.World.publication w))
  (λ id revision → Store.timestamp id revision (Store.World.reviewTimes w))

scores : Selection.Query → Store.World → Read.ScoreResult
scores q w = Read.getAssessment q
  (map Recompute.target (Recompute.beliefs (Publication.World.nodes (Store.World.publication w)))) (view w)

history : Selection.Query → Store.World → ℕ → ℕ → Read.HistoryResult
history q w offset limit = Read.history q (view w) offset limit
