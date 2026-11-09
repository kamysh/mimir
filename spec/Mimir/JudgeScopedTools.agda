{-# OPTIONS --safe #-}
-- Host-owned judge tool admission and result scope. Internal provenance reads
-- do not consume a model tool allowance. Reviewer identity is always supplied
-- by Mimir, and no model-selected mutation other than review is admitted.
module Mimir.JudgeScopedTools where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Data.List using (List; []; _∷_; _++_; length; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_; _≤?_)
import Data.Integer.Properties as Integer
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String; toList)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.RecordDecoding using (_>>=_; mapResult)
import Mimir.PublicInput as Input
import Mimir.PublicRequest as Public
import Mimir.PublicEncoding as Encoding
import Mimir.LearningWire as Wire
import Mimir.LearningInput as LearningInput
import Mimir.LearningStateWire as StateWire
import Mimir.ReviewObservation as Observation
import Mimir.ExperienceSchema as Experience
import Mimir.ReviewSchema as Review
import Mimir.JudgeTools as Tools
import Mimir.ToolCatalog as Catalog
import Mimir.StructuredValue as V
import Mimir.Validation as Validation
import Mimir.StandardLibrary as Conversion
import Mimir.GraphNumerics as Numeric
import Mimir.Binary64 as Binary
import Mimir.Effects as Effects
import Mimir.SourceFailure as Source
import Mimir.McpErrors as Errors

get : String → V.Value → V.Value
get key value with Input.view value (toList key)
... | nothing = V.null
... | just result = result

put : String → V.Value → V.Value → V.Value
put key value (V.object fields) = V.object
  (filterᵇ (λ { (name , _) → not (does (name ≟Text toList key)) }) fields ++ ((toList key , value) ∷ []))
put key value _ = V.object ((toList key , value) ∷ [])

textIs : Text → V.Value → Bool
textIs expected (V.string actual) = does (expected ≟Text actual)
textIs _ _ = false

null : V.Value → Bool
null V.null = true
null _ = false

visible : Text → V.Value → Bool
visible project V.null = false
visible project value = textIs project (get "project" value) ∨ null (get "project" value)

allVisible : Text → List V.Value → Bool
allVisible project [] = true
allVisible project (row ∷ rest) = visible project row ∧ allVisible project rest

within : ℕ → ℕ → ℕ → Bool
within lower upper actual = does (lower ≤? actual) ∧ does (actual ≤? upper)

data Failure : Set where
  rejected invalidResponse transport application candidateConflict : Text → Failure
  malformedReview malformedState : V.Value → Validation.Fault → Failure
  invalidReviewSchema : Validation.Fault → Failure
  sourceFailure : Source.Failure → Failure

data Effect : Set where call : Catalog.Tool → V.Value → Effect
Reply : Effect → Set
Reply (call _ _) = Failure ⊎ V.Value
module P = Effects.Protocol Effect Reply
open P using (Script; done; ask) renaming (_>>=_ to _then_)

require : Bool → String → V.Value → Script (Failure ⊎ V.Value)
require true message value = done (inj₂ value)
require false message value = done (inj₁ (rejected (toList message)))

chain : Script (Failure ⊎ V.Value) → (V.Value → Script (Failure ⊎ V.Value)) → Script (Failure ⊎ V.Value)
chain program next = program then λ where
  (inj₁ error) → done (inj₁ error)
  (inj₂ value) → next value

module For (conversion : Conversion.Contract) (format : Encoding.Formatting) (selected : Observation.Snapshot) where
  maximum = Binary.powerMinusOne 64
  module W = Wire.Decode conversion maximum
  module S = StateWire.Decode conversion maximum
  module D = Public.Decode conversion
  module Encode = Encoding.Encode format
  source = Observation.Snapshot.experience selected
  project = Experience.Experience.project source
  selectedID = Experience.Experience.identity source
  canonicalID = Encoding.Formatting.uuidText format selectedID

  byID : Text → V.Value
  byID id = Encoding.object (("id" , V.string id) ∷ [])

  selectedCount : V.Value → Bool
  selectedCount args with Input.view args (toList "limit")
  ... | nothing = true
  ... | just raw with Input.unsigned maximum raw
  ...   | inj₁ error = false
  ...   | inj₂ count = does (1 ≤? count)

  selectedOffset : V.Value → Bool
  selectedOffset args with Input.view args (toList "offset")
  ... | nothing = true
  ... | just raw with Input.unsigned maximum raw
  ...   | inj₁ error = false
  ...   | inj₂ offset = true

  snapshot : V.Value → Failure ⊎ Observation.Snapshot
  snapshot value with S.snapshot value
  ... | inj₁ error = inj₁ (malformedState value error)
  ... | inj₂ state = inj₂ state

  visibleBelief : Text → Script (Failure ⊎ Bool)
  visibleBelief id with Input.readUUID conversion (V.string id)
  ... | inj₁ _ = done (inj₁ (rejected (toList "invalid belief id")))
  ... | inj₂ _ = ask (call Catalog.getBelief (byID id)) λ where
    (inj₁ error) → done (inj₁ error)
    (inj₂ value) → done (inj₂ (visible project value))

  reviewed : V.Value → LearningInput.Review → Script (Failure ⊎ V.Value)
  reviewed args requestedReview with does (LearningInput.Review.experienceID requestedReview ≟ selectedID) ∧
    does (LearningInput.Review.experienceRevision requestedReview Integer.≟ Observation.Snapshot.revision selected)
  ... | false = done (inj₁ (rejected (toList "review is outside pinned revision")))
  ... | true = done (inj₂ (put "review"
    (put "reviewer" (V.string (toList "mimir-judge")) (get "review" args)) args))

  reviewArguments : V.Value → Script (Failure ⊎ V.Value)
  reviewArguments args with Input.i64 (get "expected_review_revision" args)
  ... | inj₁ _ = done (inj₁ (rejected (toList "stale review token")))
  ... | inj₂ token with does (token Integer.≟ Observation.Snapshot.reviewRevision selected)
  ...   | false = done (inj₁ (rejected (toList "stale review token")))
  ...   | true with W.reviewInput (get "review" args)
  ...     | inj₁ error = done (inj₁ (malformedReview (get "review" args) error))
  ...     | inj₂ requestedReview = reviewed args requestedReview

  historyCheck : V.Value → Failure ⊎ Observation.Snapshot → Script (Failure ⊎ V.Value)
  historyCheck args (inj₁ error) = done (inj₁ error)
  historyCheck args (inj₂ state) with textIs project (V.string (Experience.Experience.project (Observation.Snapshot.experience state)))
  ... | true = done (inj₂ args)
  ... | false = done (inj₁ (invalidResponse (toList "experience moved outside selected project")))

  history : V.Value → Script (Failure ⊎ V.Value)
  history args = ask (call Catalog.getExperience (byID canonicalID)) λ where
    (inj₁ error) → done (inj₁ error)
    (inj₂ value) → historyCheck args (snapshot value)

  graphArguments : Tools.Query → V.Value → Script (Failure ⊎ V.Value)
  graphArguments Tools.explanation args = chain (require
    (selectedCount args) "limit must be positive or omitted for all matches" args)
    (λ value → require (selectedOffset value) "offset must be nonnegative or omitted" value)
  graphArguments Tools.intervention args with D.float (get "value" args)
  ... | inj₁ _ = done (inj₁ (rejected (toList "invalid intervention value")))
  ... | inj₂ value = require (Numeric.probability value) "invalid intervention value" args
  graphArguments _ args = done (inj₂ args)

  exactGraph : Tools.Query → V.Value → V.Value → Script (Failure ⊎ V.Value)
  exactGraph kind args value with textIs project (get "project" value)
  ... | false = done (inj₁ (invalidResponse (toList "cross-project graph explanation is not available to the judge")))
  ... | true = graphArguments kind args

  ownedGraph : Tools.Query → Text → V.Value → Script (Failure ⊎ V.Value)
  ownedGraph Tools.belief id args = done (inj₂ args)
  ownedGraph kind id args = ask (call Catalog.getBelief (byID id)) λ where
    (inj₁ error) → done (inj₁ error)
    (inj₂ value) → exactGraph kind args value

  graph : Tools.Query → V.Value → Script (Failure ⊎ V.Value)
  graph kind args with V.asString (get "id" args)
  ... | inj₁ _ = done (inj₁ (rejected (toList "missing belief id")))
  ... | inj₂ id = visibleBelief id then λ where
    (inj₁ error) → done (inj₁ error)
    (inj₂ false) → done (inj₁ (rejected (toList "belief is outside selected project")))
    (inj₂ true) → ownedGraph kind id args

  before : Tools.Kind → V.Value → Script (Failure ⊎ V.Value)
  before Tools.review args = reviewArguments args
  before (Tools.query Tools.lessonAssessment) args = require (textIs project (get "project" args)) "assessment is outside selected project" args
  before (Tools.query Tools.assessmentHistory) args = chain
    (require (textIs project (get "project" args)) "assessment is outside selected project" args)
    (λ value → chain (require (selectedCount value) "limit must be positive or omitted for all matches" value)
      (λ selected → require (selectedOffset selected) "offset must be nonnegative or omitted" selected))
  before (Tools.query Tools.experience) args = require (textIs canonicalID (get "id" args)) "experience is outside pinned batch" args
  before (Tools.query Tools.learningReview) args = require (textIs canonicalID (get "id" args)) "experience is outside pinned batch" args
  before (Tools.query Tools.experienceHistory) args = chain
    (require (textIs canonicalID (get "id" args)) "experience is outside pinned batch" args) history
  before (Tools.query Tools.contradictions) args = require (textIs project (get "project" args)) "query is outside selected project" args
  before (Tools.query Tools.relevant) args = chain
    (require (textIs project (get "project" args)) "query is outside selected project" args)
    (λ value → require (selectedCount value) "limit must be positive or omitted for all matches" value)
  before (Tools.query Tools.learningContext) args = before (Tools.query Tools.relevant) args
  before (Tools.query Tools.belief) args = graph Tools.belief args
  before (Tools.query Tools.explanation) args = graph Tools.explanation args
  before (Tools.query Tools.intervention) args = graph Tools.intervention args

  array : V.Value → Failure ⊎ List V.Value
  array (V.array rows) = inj₂ rows
  array _ = inj₁ (invalidResponse (toList "expected result array"))

  keepEdge : Bool → V.Value → List V.Value → List V.Value
  keepEdge true edge rest = edge ∷ rest
  keepEdge false edge rest = rest

  filterEdges : List V.Value → Script (Failure ⊎ List V.Value)
  filterEdges [] = done (inj₂ [])
  filterEdges (edge ∷ rest) with V.asString (get "from_id" edge)
  ... | inj₁ _ = done (inj₁ (invalidResponse (toList "invalid explanation edge")))
  ... | inj₂ id = visibleBelief id then λ where
    (inj₁ error) → done (inj₁ error)
    (inj₂ keep) → filterEdges rest then λ where
      (inj₁ error) → done (inj₁ error)
      (inj₂ later) → done (inj₂ (keepEdge keep edge later))

  checkTargets : List V.Value → Script (Failure ⊎ ⊤)
  checkTargets [] = done (inj₂ tt)
  checkTargets (row ∷ rest) with V.asString (get "id" row)
  ... | inj₁ _ = done (inj₁ (invalidResponse (toList "invalid intervention target")))
  ... | inj₂ id = visibleBelief id then λ where
    (inj₁ error) → done (inj₁ error)
    (inj₂ false) → done (inj₁ (invalidResponse (toList "intervention crosses selected project")))
    (inj₂ true) → checkTargets rest

  filterPairs : List V.Value → Script (Failure ⊎ List V.Value)
  filterPairs [] = done (inj₂ [])
  filterPairs ((V.array (V.string a ∷ V.string b ∷ [])) ∷ rest) = visibleBelief a then λ where
    (inj₁ error) → done (inj₁ error)
    (inj₂ false) → filterPairs rest
    (inj₂ true) → visibleBelief b then λ where
      (inj₁ error) → done (inj₁ error)
      (inj₂ false) → filterPairs rest
      (inj₂ true) → filterPairs rest then λ where
        (inj₁ error) → done (inj₁ error)
        (inj₂ later) → done (inj₂ (V.array (V.string a ∷ V.string b ∷ []) ∷ later))
  filterPairs (_ ∷ _) = done (inj₁ (invalidResponse (toList "invalid contradiction pair")))

  afterValue : Tools.Kind → V.Value → Script (Failure ⊎ V.Value)
  afterValue (Tools.query Tools.experience) value with snapshot value
  ... | inj₁ error = done (inj₁ error)
  ... | inj₂ state with does (Experience.Experience.identity (Observation.Snapshot.experience state) ≟ selectedID) ∧
    textIs project (V.string (Experience.Experience.project (Observation.Snapshot.experience state)))
  ...   | true = done (inj₂ value)
  ...   | false = done (inj₁ (invalidResponse (toList "MCP returned out-of-scope experience")))
  afterValue (Tools.query Tools.relevant) value with array (get "beliefs" value)
  ... | inj₁ error = done (inj₁ error)
  ... | inj₂ rows with allVisible project rows
  ...   | true = done (inj₂ value)
  ...   | false = done (inj₁ (invalidResponse (toList "MCP returned out-of-scope beliefs")))
  afterValue (Tools.query Tools.learningContext) value with array (get "beliefs" value) | array (get "patterns" value)
  ... | inj₁ error | _ = done (inj₁ error)
  ... | _ | inj₁ error = done (inj₁ error)
  ... | inj₂ beliefs | inj₂ patterns with allVisible project beliefs ∧ allVisible project (Data.List.map (get "pattern") patterns)
  ...   | true = done (inj₂ value)
  ...   | false = done (inj₁ (invalidResponse (toList "MCP returned out-of-scope learning context")))
  afterValue (Tools.query Tools.explanation) value with array (get "incoming_edges" value)
  ... | inj₁ error = done (inj₁ error)
  ... | inj₂ edges = filterEdges edges then λ where
    (inj₁ error) → done (inj₁ error)
    (inj₂ filtered) → done (inj₂ (put "incoming_edges" (V.array filtered) value))
  afterValue (Tools.query Tools.intervention) value with array value
  ... | inj₁ error = done (inj₁ error)
  ... | inj₂ rows = checkTargets rows then λ where
    (inj₁ error) → done (inj₁ error)
    (inj₂ tt) → done (inj₂ value)
  afterValue (Tools.query Tools.contradictions) value with array value
  ... | inj₁ error = done (inj₁ error)
  ... | inj₂ rows = filterPairs rows then λ where
    (inj₁ error) → done (inj₁ error)
    (inj₂ filtered) → done (inj₂ (V.array filtered))
  afterValue _ value = done (inj₂ value)

  after : Tools.Kind → V.Value → Script (Failure ⊎ V.Value)
  after kind value with Errors.AgentCorrection.inspect value
  ... | inj₁ failure = done (inj₁ (invalidResponse (Validation.Fault.explanation failure)))
  ... | inj₂ (just correction) = done (inj₂ value)
  ... | inj₂ nothing = afterValue kind value

  correctionIsNotParsedAsSearchResults : ∀ kind value correction →
    Errors.AgentCorrection.inspect value ≡ inj₂ (just correction) →
    after kind value ≡ done (inj₂ value)
  correctionIsNotParsedAsSearchResults kind value correction valid rewrite valid = refl

  correctionMakesNoAdditionalScopeCalls : ∀ kind value correction events result →
    Errors.AgentCorrection.inspect value ≡ inj₂ (just correction) →
    P.Runs (after kind value) events result → events ≡ [] × result ≡ inj₂ value
  correctionMakesNoAdditionalScopeCalls kind value correction events result valid execution
    rewrite valid = P.completedCannotProduceEffects execution

  run : Text → V.Value → Script (Failure ⊎ V.Value)
  run name args@(V.object fields) with Tools.decode name
  ... | inj₁ _ = done (inj₁ (rejected (toList "tool is not allowed for judge")))
  ... | inj₂ kind = chain (before kind args) (λ admitted → chain
    (ask (call (Tools.operation kind) admitted) done) (after kind))
  run name _ = done (inj₁ (rejected (toList "tool arguments must be an object")))
