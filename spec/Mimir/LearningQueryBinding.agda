{-# OPTIONS --safe #-}
-- Statement-snapshot bindings for learning read APIs. Current-review/history
-- use raw JSONB projections; typed state/assessment queries use decoded views.
-- Both are READ COMMITTED observations, never a transaction-wide snapshot.
module Mimir.LearningQueryBinding where

open import Data.Product using (Σ)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Mimir.ApplicationStore as Physical
import Mimir.LearningQueryProtocol as Query
import Mimir.LearningHistoryWire as Raw
import Mimir.DatabaseReadCommitted as Committed

module Bind (typed : Committed.Contract Physical.World) (raw : Committed.Contract Raw.Database) where
  module T = Committed.Contract typed
  module R = Committed.Contract raw

  Reply : (effect : Query.Effect) → Query.Reply effect → Set
  Reply Query.beginRead value = ⊤
  Reply (Query.dropTransaction tx) value = ⊤
  Reply (Query.select tx statement) (inj₁ error) = ⊤
  Reply (Query.select tx statement) (inj₂ value) = Σ T.Read (λ event → value ≡ Physical.learningView (T.snapshot event))
  Reply (Query.readReviewHeader id) (inj₁ error) = ⊤
  Reply (Query.readReviewHeader id) (inj₂ value) = Σ R.Read (λ event → value ≡ Raw.readCurrent id (R.snapshot event))
  Reply (Query.readHistoryRows kind id) (inj₁ error) = ⊤
  Reply (Query.readHistoryRows kind id) (inj₂ rows) = Σ R.Read (λ event → rows ≡ Raw.readHistory kind id (R.snapshot event))
