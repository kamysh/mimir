{-# OPTIONS --safe #-}
-- The complete project ownership closure is published in one transaction.
-- Its returned count is the observed belief count plus the observed chunk
-- count; patterns are removed but do not contribute to that count.
module Mimir.ProjectDeletion where

open import Data.Bool using (Bool; true; false; not; _∨_; _∧_)
open import Data.List using (List; []; _∷_; filterᵇ; map; length; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_; z≤n) renaming (_≟_ to _≟ℕ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Relation.Nullary using (yes; no; does)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.GraphWrites as Writes
import Mimir.LearningStore as Learning
import Mimir.LearningHistoryWire as RawHistory
import Mimir.ReviewPreparationPublication as Publication
import Mimir.ReviewLedger as Ledger
import Mimir.ExperienceRead as Read
import Mimir.ExperienceSchema as Experience
import Mimir.ReviewObservation as Observation
import Mimir.CandidateRegistry as Candidates
import Mimir.AssessmentWrites as Assessments
import Mimir.ItemOwners as Owners
import Mimir.RetrievalRanking as Ranking
import Mimir.DocumentStore as Documents
import Mimir.LearningTransaction as Transaction
import Mimir.DatabaseTransaction as DB
import Mimir.Effects as Effects

open import Data.String using (toList; fromList)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
import Mimir.CandidateGraph as Graph
import Mimir.ReviewEdges as Edges
import Mimir.Recovery as Recovery
import Mimir.StructuredValue as Wire
import Mimir.McpErrors as Errors
import Mimir.Validation as Validation
open import Mimir.SourceReview using (_≟Text_)
import Mimir.RecordDecoding as Decode
import Mimir.JsonObjects as Objects
open import Data.Empty using (⊥; ⊥-elim)

-- These list laws state both halves of deletion: every owned row is removed,
-- and every retained row survives. They quantify over all predicates and rows.
module Retention {A : Set} (owned : A → Bool) where
  retain : List A → List A
  retain = filterᵇ (λ value → not (owned value))

  excludesOwned : ∀ values → All (λ value → owned value ≡ false) (retain values)
  excludesOwned [] = []
  excludesOwned (value ∷ rest) with owned value in equality
  ... | true = excludesOwned rest
  ... | false = equality ∷ excludesOwned rest

  preservesUnowned : ∀ value values → owned value ≡ false →
    Any (value ≡_) values → Any (value ≡_) (retain values)
  preservesUnowned value (.value ∷ rest) retained (here refl) rewrite retained = here refl
  preservesUnowned value (head ∷ rest) retained (there present) with owned head
  ... | true = preservesUnowned value rest retained present
  ... | false = there (preservesUnowned value rest retained present)

ownedExperiences : Text → Learning.World → List ℕ
ownedExperiences project w = map Read.identity (filterᵇ (Read.scopeMatches (just project)) (Learning.World.current w))

-- SQL foreign-key cascades remove relational history and ownership. Graph
-- nodes/edges are not FK targets; the preceding graph DELETE phases own them.
forgetLearning : Text → Store.World → Store.World
forgetLearning project w = record w { learning = record learn
  { current = filterᵇ (λ r → keep (Read.identity r)) (Learning.World.current learn)
  ; sources = filterᵇ (λ r → keep (Experience.Experience.identity (Learning.SourceVersion.payload r))) (Learning.World.sources learn)
  ; reviewTimes = filterᵇ (λ r → keep (Learning.ReviewTime.experience r)) (Learning.World.reviewTimes learn)
  ; itemKeys = keys
  ; publication = record pub
    { ledger = Ledger.world cells histories
    ; registry = filterᵇ (λ r → keep (Candidates.Entry.experienceID r)) (Publication.World.registry pub)
    ; assessments = filterᵇ (λ r → keep (Assessments.Row.experience r)) (Publication.World.assessments pub)
    ; owners = owners } } }
  where
  learn = Store.World.learning w
  pub = Learning.World.publication learn
  ledger = Publication.World.ledger pub
  ids = ownedExperiences project learn
  keep : ℕ → Bool
  keep id = not (Ranking.member id ids)
  keys : ℕ → Text → Maybe ℕ
  keys experience name with Ranking.member experience ids
  ... | true = nothing
  ... | false = Learning.World.itemKeys learn experience name
  cells : ℕ → Ledger.R.Cell
  cells id with Ranking.member id ids
  ... | true = Ledger.R.cell [] 0 0 0 nothing z≤n
  ... | false = Ledger.World.cells ledger id
  histories : ℕ → List Ledger.Version
  histories id with Ranking.member id ids
  ... | true = []
  ... | false = Ledger.World.histories ledger id
  owners : Owners.Registry
  owners id with Publication.World.owners pub id
  ... | nothing = nothing
  ... | just (owner , provenance) with Ranking.member owner ids
  ...   | true = nothing
  ...   | false = just (owner , provenance)

forgottenExperienceKeysRemoved : ∀ project before experience name →
  Ranking.member experience (ownedExperiences project (Store.World.learning before)) ≡ true →
  Learning.World.itemKeys (Store.World.learning (forgetLearning project before)) experience name ≡ nothing
forgottenExperienceKeysRemoved project before experience name removed rewrite removed = refl

otherExperienceKeysPreserved : ∀ project before experience name →
  Ranking.member experience (ownedExperiences project (Store.World.learning before)) ≡ false →
  Learning.World.itemKeys (Store.World.learning (forgetLearning project before)) experience name ≡
    Learning.World.itemKeys (Store.World.learning before) experience name
otherExperienceKeysPreserved project before experience name retained rewrite retained = refl

projectChunks : Text → Store.World → List ℕ
projectChunks project w = map Documents.Chunk.identity
  (filterᵇ (λ c → Writes.tagged project (Documents.Chunk.project c)) (Store.World.chunks w))

-- Ownership is captured from the ORIGINAL world. Vector selection must not
-- depend on roots still being discoverable in the resulting world.
record Closure : Set where
  constructor closure
  field beliefs patterns chunks : List ℕ

ownership : Text → Store.World → Closure
ownership project before = closure (Writes.projectBeliefs project before)
  (Writes.projectPatterns project before) (projectChunks project before)

ownedNode : Text → Graph.Node → Bool
ownedNode project node = Writes.tagged project (Graph.nodeProject node)

ownedEdge : Closure → Edges.Edge → Bool
ownedEdge selected link = Ranking.member (Edges.Edge.from link) roots ∨ Ranking.member (Edges.Edge.to link) roots
  where roots = Closure.beliefs selected ++ Closure.patterns selected

ownedGround : Closure → Store.Ground → Bool
ownedGround selected edge = Ranking.member (Store.Ground.belief edge) (Closure.beliefs selected) ∨
  Ranking.member (Store.Ground.chunk edge) (Closure.chunks selected)

-- One resulting state, defined field by field from ownership. This function
-- contains no SQL statements, commit order, receipt or execution cursor.
historyOwned : Text → RawHistory.Head → Bool
historyOwned project header = does (project ≟Text RawHistory.Head.project header)

historyIDs : Text → Store.World → List ℕ
historyIDs project before = map RawHistory.Head.identity
  (filterᵇ (historyOwned project) (RawHistory.Database.heads (Store.World.history before)))

ownedHistoryRow : Text → Store.World → RawHistory.Row → Bool
ownedHistoryRow project before storedRow = Ranking.member (RawHistory.Row.experience storedRow) (historyIDs project before)

eraseHistory : Text → Store.World → RawHistory.Database
eraseHistory project before = record
  { heads = Retention.retain (historyOwned project) (RawHistory.Database.heads prior)
  ; sourceRows = Retention.retain (ownedHistoryRow project before) (RawHistory.Database.sourceRows prior)
  ; reviewRows = Retention.retain (ownedHistoryRow project before) (RawHistory.Database.reviewRows prior) }
  where prior = Store.World.history before

eraseProject : Text → Store.World → Store.World
eraseProject project before = record before
  { learning = record learn
      { publication = record publication
          { nodes = Retention.retain (ownedNode project) (Store.nodes before)
          ; edges = Retention.retain (ownedEdge selected) (Publication.World.edges publication) }
      ; independentOrigins = Retention.retain (λ row → Ranking.member (proj₁ row) roots)
          (Learning.World.independentOrigins learn) }
  ; chunks = Retention.retain (λ chunk → Writes.tagged project (Documents.Chunk.project chunk)) (Store.World.chunks before)
  ; beliefVectors = Retention.retain (λ row → Ranking.member (proj₁ row) (Closure.beliefs selected)) (Store.World.beliefVectors before)
  ; chunkVectors = Retention.retain (λ row → Ranking.member (proj₁ row) (Closure.chunks selected)) (Store.World.chunkVectors before)
  ; grounds = Retention.retain (ownedGround selected) (Store.World.grounds before)
  ; history = eraseHistory project before }
  where
  selected = ownership project before
  roots = Closure.beliefs selected ++ Closure.patterns selected
  learn = Store.World.learning (forgetLearning project before)
  publication = Learning.World.publication learn

noProjectHistoryHeaders : ∀ project before → All (λ header → historyOwned project header ≡ false)
  (RawHistory.Database.heads (Store.World.history (eraseProject project before)))
noProjectHistoryHeaders project before = Retention.excludesOwned (historyOwned project)
  (RawHistory.Database.heads (Store.World.history before))

noOriginalProjectSourceHistory : ∀ project before → All (λ row → ownedHistoryRow project before row ≡ false)
  (RawHistory.Database.sourceRows (Store.World.history (eraseProject project before)))
noOriginalProjectSourceHistory project before = Retention.excludesOwned (ownedHistoryRow project before)
  (RawHistory.Database.sourceRows (Store.World.history before))

noOriginalProjectReviewHistory : ∀ project before → All (λ row → ownedHistoryRow project before row ≡ false)
  (RawHistory.Database.reviewRows (Store.World.history (eraseProject project before)))
noOriginalProjectReviewHistory project before = Retention.excludesOwned (ownedHistoryRow project before)
  (RawHistory.Database.reviewRows (Store.World.history before))

noOriginalBeliefVectors : ∀ project before →
  All (λ row → Ranking.member (proj₁ row) (Closure.beliefs (ownership project before)) ≡ false)
    (Store.World.beliefVectors (eraseProject project before))
noOriginalBeliefVectors project before = Retention.excludesOwned _ (Store.World.beliefVectors before)

noOriginalChunkVectors : ∀ project before →
  All (λ row → Ranking.member (proj₁ row) (Closure.chunks (ownership project before)) ≡ false)
    (Store.World.chunkVectors (eraseProject project before))
noOriginalChunkVectors project before = Retention.excludesOwned _ (Store.World.chunkVectors before)

noProjectNodes : ∀ project before → All (λ node → ownedNode project node ≡ false) (Store.nodes (eraseProject project before))
noProjectNodes project before = Retention.excludesOwned (ownedNode project) (Store.nodes before)

noProjectChunks : ∀ project before → All (λ chunk → Writes.tagged project (Documents.Chunk.project chunk) ≡ false)
  (Store.World.chunks (eraseProject project before))
noProjectChunks project before = Retention.excludesOwned _ (Store.World.chunks before)

noOwnedGrounds : ∀ project before → All (λ edge → ownedGround (ownership project before) edge ≡ false)
  (Store.World.grounds (eraseProject project before))
noOwnedGrounds project before = Retention.excludesOwned _ (Store.World.grounds before)

noOwnedEdges : ∀ project before → All (λ link → ownedEdge (ownership project before) link ≡ false)
  (Publication.World.edges (Learning.World.publication (Store.World.learning (eraseProject project before))))
noOwnedEdges project before = Retention.excludesOwned _
  (Publication.World.edges (Learning.World.publication (Store.World.learning before)))

noOriginalExperiences : ∀ project before →
  All (λ row → Ranking.member (Read.identity row) (ownedExperiences project (Store.World.learning before)) ≡ false)
    (Learning.World.current (Store.World.learning (eraseProject project before)))
noOriginalExperiences project before = Retention.excludesOwned _ (Learning.World.current (Store.World.learning before))

otherBeliefVectorPreserved : ∀ project before row →
  Ranking.member (proj₁ row) (Closure.beliefs (ownership project before)) ≡ false →
  Any (row ≡_) (Store.World.beliefVectors before) →
  Any (row ≡_) (Store.World.beliefVectors (eraseProject project before))
otherBeliefVectorPreserved project before row = Retention.preservesUnowned _ row (Store.World.beliefVectors before)

otherChunkVectorPreserved : ∀ project before row →
  Ranking.member (proj₁ row) (Closure.chunks (ownership project before)) ≡ false →
  Any (row ≡_) (Store.World.chunkVectors before) →
  Any (row ≡_) (Store.World.chunkVectors (eraseProject project before))
otherChunkVectorPreserved project before row = Retention.preservesUnowned _ row (Store.World.chunkVectors before)

otherNodePreserved : ∀ project before node → ownedNode project node ≡ false →
  Any (node ≡_) (Store.nodes before) → Any (node ≡_) (Store.nodes (eraseProject project before))
otherNodePreserved project before node = Retention.preservesUnowned _ node (Store.nodes before)

otherChunkPreserved : ∀ project before chunk → Writes.tagged project (Documents.Chunk.project chunk) ≡ false →
  Any (chunk ≡_) (Store.World.chunks before) → Any (chunk ≡_) (Store.World.chunks (eraseProject project before))
otherChunkPreserved project before chunk = Retention.preservesUnowned _ chunk (Store.World.chunks before)

otherEdgePreserved : ∀ project before link → ownedEdge (ownership project before) link ≡ false →
  Any (link ≡_) (Publication.World.edges (Learning.World.publication (Store.World.learning before))) →
  Any (link ≡_) (Publication.World.edges (Learning.World.publication (Store.World.learning (eraseProject project before))))
otherEdgePreserved project before link = Retention.preservesUnowned _ link
  (Publication.World.edges (Learning.World.publication (Store.World.learning before)))

deletedCount : Text → Store.World → ℕ
deletedCount project before = length (Writes.projectBeliefs project before) + length (projectChunks project before)

intent : Recovery.Business.Intent Text
intent = record
  { intended = eraseProject
  ; expectedReply = λ project before → Wire.object ((toList "deleted" , Wire.unsigned (deletedCount project before)) ∷ []) }

-- The registered request has no caller-selected deletion policy. Its only
-- business argument is the project; the token identifies the original work.
module Registered where
  record Input : Set where
    constructor input
    field token : ℕ; project : Text

  operationName = toList "delete_project"
  boundaryName = toList "store.delete_project"
  stepKey = toList "[\"store.delete_project\",null]"
  resultKey = toList "@operation-result"

  fieldText : Text → Maybe Wire.Value → Bool
  fieldText expected (just (Wire.string actual)) = does (actual ≟Text expected)
  fieldText expected _ = false

  fieldNull : Maybe Wire.Value → Bool
  fieldNull (just Wire.null) = true
  fieldNull _ = false

  fieldFalse : Maybe Wire.Value → Bool
  fieldFalse (just (Wire.boolean false)) = true
  fieldFalse _ = false

  singleton : (Wire.Value → Bool) → Maybe Wire.Value → Bool
  singleton check (just (Wire.array (value ∷ []))) = check value
  singleton check _ = false

  fields : List Text → (Wire.Object.View → Bool) → Wire.Value → Bool
  fields names check raw with Decode.readRecord Objects.forbid Objects.rejectKnownRepeated names
    (λ view → inj₂ (check view)) raw
  ... | inj₁ _ = false
  ... | inj₂ result = result

  shapeMatches : Wire.Value → Bool
  shapeMatches = fields (toList "site" ∷ toList "may_repeat" ∷ []) λ view →
    fieldText boundaryName (view (toList "site")) ∧ fieldFalse (view (toList "may_repeat"))

  stepMatches : Wire.Value → Bool
  stepMatches = fields (toList "site" ∷ toList "key" ∷ toList "id" ∷ []) λ view →
    fieldText boundaryName (view (toList "site")) ∧ fieldNull (view (toList "key")) ∧
      fieldText stepKey (view (toList "id"))

  planMatches : Wire.Value → Bool
  planMatches = fields (toList "operation" ∷ toList "shape" ∷ toList "steps" ∷ []) λ view →
    fieldText operationName (view (toList "operation")) ∧
      singleton shapeMatches (view (toList "shape")) ∧ singleton stepMatches (view (toList "steps"))

  argumentsMatch : Text → Wire.Value → Bool
  argumentsMatch project = fields (toList "project" ∷ []) λ view → fieldText project (view (toList "project"))

  settingsMatch : Wire.Value → Bool
  settingsMatch (Wire.object []) = true
  settingsMatch _ = false

  binding : ℕ → List Store.BindingRow → Maybe Store.BindingRow
  binding token [] = nothing
  binding token (row ∷ rest) with token ≟ℕ Store.BindingRow.token row
  ... | yes _ = just row
  ... | no _ = binding token rest

  plan : ℕ → List Store.PlanRow → Maybe Wire.Value
  plan token [] = nothing
  plan token (row ∷ rest) with token ≟ℕ Store.PlanRow.token row
  ... | yes _ = just (Store.PlanRow.plan row)
  ... | no _ = plan token rest

  -- These checks read immutable request and plan metadata, never business rows
  -- or saved replies. Publication cannot turn a valid request into a new one.
  blockedBy : Input → List Store.BindingRow → List Store.PlanRow → Maybe Text
  blockedBy request bindings plans with binding (Input.token request) bindings
  ... | nothing = just (toList "Unknown operation binding. Reserve and bind the original delete_project request before publishing; read the token outcome if a reply was lost.")
  ... | just original with does (Store.BindingRow.operation original ≟Text operationName) ∧
    argumentsMatch (Input.project request) (Store.BindingRow.arguments original) ∧ settingsMatch (Store.BindingRow.settings original)
  ...   | false = just (toList "This token belongs to a different request. Read its original binding and outcome; retain that request or ask the user before starting distinct work.")
  ...   | true with plan (Input.token request) plans
  ...     | nothing = just (toList "The original operation has no saved plan. Prepare its registered deletion plan before publishing; do not invent a replacement token.")
  ...     | just saved with planMatches saved
  ...       | false = just (toList "The saved plan disagrees with the registered deletion boundary. Read its plan and outcome and ask the user how to resolve it; do not repeat data changes.")
  ...       | true = nothing

  blocked : Input → Store.World → Maybe Text
  blocked request before = blockedBy request
    (Store.OperationTables.bindings (Store.World.operations before))
    (Store.OperationTables.plans (Store.World.operations before))

  correction : Store.World → Text → Wire.Value
  correction before explanation = Errors.AgentCorrection.emitCorrection
    {World = Store.World} {before = before} {after = before}
    (Errors.AgentCorrection.certified
      (Errors.AgentCorrection.claim
        (Errors.AgentCorrection.item Errors.AgentCorrection.arguments
          (Validation.fault [] Validation.malformedInput (fromList explanation))
          (toList "The original bound request and its registered saved plan") explanation) []) refl)

  data Mode : Set where
    needsInput : Text → Mode
    replay : Wire.Value → Mode
    publish : Mode

  mode : Input → Store.World → Mode
  mode request before with blocked request before
  ... | just explanation = needsInput explanation
  ... | nothing with Store.lookupSaved before (Input.token request) stepKey |
    Store.lookupSaved before (Input.token request) resultKey
  ...   | just saved | just final = replay saved
  ...   | nothing | nothing = publish
  ...   | _ | _ = needsInput (toList "Only one final answer was saved. Read the step answer and operation outcome and ask the user to resolve this older operation; do not repeat its data changes or invent an answer.")

  answer : Input → Store.World → Wire.Value
  answer request before = Recovery.Business.Intent.expectedReply intent (Input.project request) before

  -- Independent desired state: remove the complete original ownership closure
  -- and retain both original answers. No discovery or commit sequence occurs.
  finalWorld : Input → Store.World → Store.World
  finalWorld request before = record erased
    { operations = record tables { savedReplies =
        Store.savedReplyRow token resultKey reply ∷ Store.savedReplyRow token stepKey reply ∷
          Store.OperationTables.savedReplies tables } }
    where
    token = Input.token request
    reply = answer request before
    erased = eraseProject (Input.project request) before
    tables = Store.World.operations before

  intended : Input → Store.World → Store.World
  intended request before with mode request before
  ... | publish = finalWorld request before
  ... | _ = before

  expectedReply : Input → Store.World → Wire.Value
  expectedReply request before with mode request before
  ... | needsInput explanation = correction before explanation
  ... | replay saved = saved
  ... | publish = answer request before

  registeredIntent : Recovery.Business.Intent Input
  registeredIntent = record { intended = intended; expectedReply = expectedReply }

  execute : Input → Store.World → Store.World × Wire.Value
  execute request before with mode request before
  ... | needsInput explanation = before , correction before explanation
  ... | replay saved = before , saved
  ... | publish = finalWorld request before , answer request before

  correct : ∀ request before → execute request before ≡
    Recovery.Business.expected registeredIntent (Recovery.Business.invocation request before)
  correct request before with mode request before
  ... | needsInput explanation = refl
  ... | replay saved = refl
  ... | publish = refl

  publicationPreservesAdmission : ∀ request before →
    blocked request (finalWorld request before) ≡ blocked request before
  publicationPreservesAdmission request before = refl

  publishedResultReadable : ∀ request before →
    Store.lookupSaved (finalWorld request before) (Input.token request) resultKey ≡ just (answer request before)
  publishedResultReadable request before = Store.headReplyReadable (Input.token request) resultKey (answer request before)
    (Store.savedReplyRow (Input.token request) stepKey (answer request before) ∷
      Store.OperationTables.savedReplies (Store.World.operations before))

  publishedStepReadable : ∀ request before →
    Store.lookupSaved (finalWorld request before) (Input.token request) stepKey ≡ just (answer request before)
  publishedStepReadable request before with Store.replyKey? (Input.token request) stepKey
    (Store.savedReplyRow (Input.token request) resultKey (answer request before))
  ... | no _ = Store.headReplyReadable (Input.token request) stepKey (answer request before)
    (Store.OperationTables.savedReplies (Store.World.operations before))
  ... | yes (_ , impossible) with cong length impossible
  ...   | ()

  publishedMode : ∀ request before → blocked request before ≡ nothing →
    mode request (finalWorld request before) ≡ replay (answer request before)
  publishedMode request before unblocked
    rewrite publicationPreservesAdmission request before | unblocked |
      publishedStepReadable request before | publishedResultReadable request before = refl

  newRequestWasAdmitted : ∀ request before → mode request before ≡ publish → blocked request before ≡ nothing
  newRequestWasAdmitted request before fresh with blocked request before
  ... | nothing = refl
  ... | just explanation with fresh
  ...   | ()

  stable : ∀ request before →
    execute request (proj₁ (execute request before)) ≡ execute request before
  stable request before with mode request before in selected
  ... | needsInput explanation rewrite selected = refl
  ... | replay saved rewrite selected = refl
  ... | publish rewrite publishedMode request before (newRequestWasAdmitted request before selected) = refl

  statement : Recovery.Single.Statement Store.World Input
  statement = record { execute = execute; intent = registeredIntent; correct = correct }

  recoverable : Recovery.Recoverable Store.World Input
  recoverable = Recovery.Single.single statement (record { stable = stable })

  -- The extra journal fields do not weaken the independent ownership result.
  newPublicationRemovesOriginalVectors : ∀ request before →
    All (λ row → Ranking.member (proj₁ row) (Closure.beliefs (ownership (Input.project request) before)) ≡ false)
      (Store.World.beliefVectors (finalWorld request before))
  newPublicationRemovesOriginalVectors request before = noOriginalBeliefVectors (Input.project request) before

  newPublicationRemovesProjectNodes : ∀ request before →
    All (λ node → ownedNode (Input.project request) node ≡ false) (Store.nodes (finalWorld request before))
  newPublicationRemovesProjectNodes request before = noProjectNodes (Input.project request) before

  publicationHasExactlyTheErasedBusinessState : ∀ request before →
    Store.businessSnapshot (finalWorld request before) ≡ Store.businessSnapshot (eraseProject (Input.project request) before)
  publicationHasExactlyTheErasedBusinessState request before = refl

  newStateIsTheDeletionGoal : ∀ request before → mode request before ≡ publish →
    intended request before ≡ finalWorld request before
  newStateIsTheDeletionGoal request before fresh rewrite fresh = refl

  newReplyIsTheOriginalCount : ∀ request before → mode request before ≡ publish →
    expectedReply request before ≡ answer request before
  newReplyIsTheOriginalCount request before fresh rewrite fresh = refl

  module Checked = Recovery.Recoverable recoverable

  completedRetryKeepsOriginalCount : ∀ request initial interrupted final reply → mode request initial ≡ publish →
    Checked.X.Interrupted (Checked.script request) initial interrupted →
    Checked.X.Completed (Checked.script request) interrupted final reply →
    reply ≡ answer request initial
  completedRetryKeepsOriginalCount request initial interrupted final reply fresh interruption completion = trans
    (cong proj₂ (Checked.converges request initial interrupted final reply interruption completion))
    (newReplyIsTheOriginalCount request initial fresh)

  completedRetryLeavesNoOriginalVectors : ∀ request initial interrupted final reply → mode request initial ≡ publish →
    Checked.X.Interrupted (Checked.script request) initial interrupted →
    Checked.X.Completed (Checked.script request) interrupted final reply →
    All (λ row → Ranking.member (proj₁ row) (Closure.beliefs (ownership (Input.project request) initial)) ≡ false)
      (Store.World.beliefVectors final)
  completedRetryLeavesNoOriginalVectors request initial interrupted final reply fresh interruption completion =
    subst (λ state → All (λ row → Ranking.member (proj₁ row)
      (Closure.beliefs (ownership (Input.project request) initial)) ≡ false) (Store.World.beliefVectors state))
      (sym (trans (cong proj₁ (Checked.converges request initial interrupted final reply interruption completion))
        (newStateIsTheDeletionGoal request initial fresh)))
      (newPublicationRemovesOriginalVectors request initial)

module Operation (database : ℕ) where
  module T = Transaction.Over Store.World ℕ Text database 671942183

  plan : Text → Store.World → T.Decision
  plan project before = T.replace (eraseProject project before) (deletedCount project before)

  Effect = T.Effect
  Reply = T.Reply
  module E = T.E

  data Result : Set where
    transactionResult : T.Outcome → Result
    deleted : ℕ → Result

  finish : T.Outcome → E.Script Result
  finish (T.applied count) = E.done (deleted count)
  finish result = E.done (transactionResult result)

  start : Text → E.Script Result
  start project = E._>>=_ Tx.start finish
    where module Tx = T.Plan (plan project)

  Publication : Text → Store.World → DB.Receipt → Store.World → Set
  Publication project before receipt after = DB.Atomic before (eraseProject project before) receipt after

  noPartiallyDeletedPublication : ∀ project before receipt after →
    Publication project before receipt after →
    after ≡ before ⊎ after ≡ eraseProject project before
  noPartiallyDeletedPublication project before .DB.committed .(eraseProject project before) DB.committedAll = inj₂ refl
  noPartiallyDeletedPublication project before .DB.aborted .before DB.abortedNone = inj₁ refl
  noPartiallyDeletedPublication project before .DB.acknowledgementLost .before DB.unknownBefore = inj₁ refl
  noPartiallyDeletedPublication project before .DB.acknowledgementLost .(eraseProject project before) DB.unknownAfter = inj₂ refl
