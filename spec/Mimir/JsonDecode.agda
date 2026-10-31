{-# OPTIONS --safe #-}
-- Composed default-JSON decoder with nesting, complete-consumption and ordered
-- object-normalization certificates. Source/runtime correspondence is separate.
import Mimir.FloatConversion
module Mimir.JsonDecode (floatConversion : Mimir.FloatConversion.Contract) where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.JsonTreeBounds as Bounds
import Mimir.JsonTreeParser as TreeDependency
private
  module Tree = TreeDependency floatConversion
import Mimir.JsonStoredValue as Stored
import Mimir.JsonFlow as Flow
import Mimir.JsonCompletion as CompletionDependency
private
  module Completion = CompletionDependency floatConversion
import Mimir.SignedMachine as Machine

record Decoded : Set where
  constructor decoded
  field
    parsed : Bounds.Bounded 127
    value : Stored.Value
    exact : value ≡ Stored.normalize (Bounds.Bounded.tree parsed)
    canonical : Stored.Stored value

build : Bounds.Bounded 127 → Decoded
build parsed = decoded parsed (Stored.normalize (Bounds.Bounded.tree parsed)) refl (Stored.normalizedStored (Bounds.Bounded.tree parsed))

module Parser (checks : Machine.OverflowChecks) where
  module T = Tree.Parser checks
  module C = Completion.For checks

  read : ∀ input → Flow.Productive Decoded input
  read input = Flow.mapProductive build (T.boundedDocument input)

  consumesCompleteDocument : ∀ input → Completion.Complete (Flow.Productive.result (read input))
  consumesCompleteDocument input = Completion.mapProductiveComplete build (T.boundedDocument input) (C.boundedDocumentComplete input)
