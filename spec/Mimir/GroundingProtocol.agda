{-# OPTIONS --safe #-}
-- Project compatibility for explicitly cited indexed support.
module Mimir.GroundingProtocol where

open import Data.Bool using (Bool; true)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (does)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)

compatible : Maybe Text → Maybe Text → Bool
compatible nothing actual = true
compatible (just wanted) nothing = true
compatible (just wanted) (just actual) = does (wanted ≟Text actual)

-- No automatic grounding protocol remains: source support is supplied and
-- validated explicitly before paired belief publication.
