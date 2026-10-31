{-# OPTIONS --safe #-}
-- Public scalar helpers and diagnostic projections which do not issue MCP
-- requests. Float arithmetic and formatting remain standard-library contracts.
module Mimir.CoreLibrary where

open import Data.Bool using (true; false)
open import Data.Float.Base using (Float; _+_; _-_; _*_; _**_)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Nat using (ℕ)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.GraphNumerics as Numeric
import Mimir.PosteriorComputation as Beta
import Mimir.CandidateGraph as Graph
import Mimir.ConfigurationValues as Config

probability : Float → Maybe Float
probability value with Numeric.probability value
... | false = nothing
... | true = just value

-- Probability::attenuate returns its wrapper directly; the inference helpers
-- run Probability::new after clamping and can therefore reject NaN.
attenuate : Float → Float → Float
attenuate value factor = Beta.clamp (value * factor)

defeat : Float → Float → Float → Maybe Float
defeat target source weight = probability (Beta.clamp (target * (1.0 - weight * source)))

support : Float → Float → Float → Maybe Float
support target source weight = probability (Beta.clamp (target + ((1.0 - target) * weight) * source))

decay : Float → Float → Float → Maybe Float
decay value days factor = probability (Beta.clamp (value * (factor ** days)))

strength : Graph.BeliefValues → Float
strength belief = Graph.BeliefValues.alpha belief + Graph.BeliefValues.beta belief

refresh : Graph.BeliefValues → Graph.BeliefValues
refresh belief = record belief { probability = Beta.mean posterior; confidence = Beta.confidence posterior }
  where posterior = Beta.beta (Graph.BeliefValues.alpha belief) (Graph.BeliefValues.beta belief)

record DatabaseDebug : Set where
  constructor databaseDebug
  field host dbname user : Text
        port : ℕ
        password pgpassfile : Maybe Text
        mode : Config.Mode

databaseDebugView : Config.Database → DatabaseDebug
databaseDebugView config = databaseDebug (Config.Database.host config) (Config.Database.dbname config)
  (Config.Database.user config) (Config.Database.port config)
  (map (λ _ → toList "[REDACTED]") (Config.Database.password config))
  (Config.Database.pgpassfile config) (Config.Database.mode config)

-- DatabaseDebug is rendered non-exhaustively; certificate/key fields are
-- absent. Config's custom Debug emits one constant rather than field values.
configDebug : Config.Config → Text
configDebug _ = toList "Config { contents: [REDACTED] }"

configDebugIndependent : ∀ before after → configDebug before ≡ configDebug after
configDebugIndependent before after = refl

refreshPreservesIdentity : ∀ belief → Graph.BeliefValues.identity (refresh belief) ≡ Graph.BeliefValues.identity belief
refreshPreservesIdentity belief = refl
