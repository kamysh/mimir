{-# OPTIONS --safe #-}
-- Compose the certified public search with the existing concrete learning
-- assembly. Inputs contain no selected identities or desired outcome counts.
module Mimir.PublicLearningContextRecovery where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.CandidateGraph as Graph
import Mimir.ConfigurationValues as Config
import Mimir.LearningContext as Learning
import Mimir.LearningContextProtocol as Context
import Mimir.PreparedRetrieval as Prepared
import Mimir.RetrievalRanking as Ranking
import Mimir.RetrievalProtocol as Retrieval
import Mimir.PublicRetrievalRecovery as Search
import Mimir.OrderedRetrieval as Ordered
import Mimir.StorageReadBinding as Database
import Mimir.PublicRequest as Public
import Mimir.Recovery as Recovery
import Mimir.McpErrors as Errors
import Mimir.Validation as Validation

module Correction = Errors.AgentCorrection

record Request : Set where
  constructor contextSearch
  field context project : Text; selection : Ranking.Selection

publicRequest : Request → Public.Request
publicRequest request = Public.learningContext (Request.context request) (Request.project request) (Request.selection request)

projectCorrection : Correction.Claim
projectCorrection = Correction.claim
  (Correction.item Correction.arguments
    (Validation.fault (Validation.key "project" ∷ []) Validation.emptyText "The supplied project is blank or contains only whitespace.")
    (toList "The explicit, nonblank project for the intended learning context.")
    (toList "Supply the intended project from the task context and retry. If it is not known, ask the user. Do not invent a project or substitute an unrelated one.")) []

enabled : Maybe Config.Embeddings → Bool
enabled nothing = false
enabled (just _) = true

module Run (arithmetic : Ranking.F32) (unicode : Ranking.Unicode)
  (database : Database.VectorOperations) (coreConfiguration : Config.Config)
  (textBefore : Text → Text → Bool) where
  module Base = Search.Run arithmetic unicode database coreConfiguration
  module I = Ordered.Intent arithmetic unicode database
  module Assembly = Context.Assembly unicode textBefore
  module E = Base.E
  module X = Base.X

  query : Request → Search.Request
  query request = Search.fromFields (Request.context request) (Request.selection request)
    (just (Request.project request)) nothing false nothing

  retrievalKeepsTheRequestedScopeAndSelection : ∀ request → Search.publicRequest (query request) ≡
    Public.relevant (Request.context request) (Request.selection request) (just (Request.project request)) nothing false nothing
  retrievalKeepsTheRequestedScopeAndSelection request = refl

  admitted : Request → Bool
  admitted request = Learning.admitted (Request.project request) (Request.selection request)

  assembled : Request → Store.World → Prepared.Preparation → Assembly.Input
  assembled request snapshot preparation = Assembly.selected
    (Context.contextRequest (Request.context request) (Request.project request) (Request.selection request)
      (enabled (Config.Config.embed coreConfiguration)))
    (map Graph.BeliefValues.identity (Retrieval.Report.beliefs selected))
    (Retrieval.Coverage.semantic (Retrieval.Report.retrieval selected))
    where selected = I.answer (Search.Request.search (query request)) snapshot preparation

  answer : Request → Store.World → Prepared.Preparation → Assembly.Result
  answer request snapshot preparation = Assembly.answer (assembled request snapshot preparation) snapshot

  snapshotOf : Base.Result → Store.World
  snapshotOf (Base.completed _ _ snapshot _ _) = snapshot

  preparationOf : Base.Result → Prepared.Preparation
  preparationOf (Base.completed _ _ _ receipt _) = Base.preparation receipt

  data Result : Set where
    needsInput : Request → Correction.Claim → Result
    contextResult : Base.Result → Assembly.Result → Result

  attach : Request → Base.Result → Result
  attach request source = contextResult source (answer request (snapshotOf source) (preparationOf source))

  private
    mapScript : (Base.Result → Result) → E.Script Base.Result → E.Script Result
    mapScript convert (E.done source) = E.done (convert source)
    mapScript convert (E.ask effect continuation) = E.ask effect (λ reply → mapScript convert (continuation reply))

    mapRun : ∀ convert program events source → E.Runs program events source →
      E.Runs (mapScript convert program) events (convert source)
    mapRun convert .(E.done source) .[] source (E.returned .source) = E.returned (convert source)
    mapRun convert .(E.ask effect continuation) ._ source (E.replied effect continuation reply later) =
      E.replied effect _ reply (mapRun convert (continuation reply) _ source later)

    unmapRun : ∀ convert program events result → E.Runs (mapScript convert program) events result →
      Σ Base.Result (λ source → E.Runs program events source × result ≡ convert source)
    unmapRun convert (E.done source) .[] .(convert source) (E.returned .(convert source)) = source , E.returned source , refl
    unmapRun convert (E.ask effect continuation) ._ result (E.replied .effect _ reply later)
      with unmapRun convert (continuation reply) _ result later
    ... | source , execution , same = source , E.replied effect continuation reply execution , same

  branch : Request → Bool → E.Script Result
  branch request false = E.done (needsInput request projectCorrection)
  branch request true = mapScript (attach request) (Base.script (query request))

  script : Request → E.Script Result
  script request = branch request (admitted request)

  invalidProjectDoesNotStartWork : ∀ request → admitted request ≡ false →
    script request ≡ E.done (needsInput request projectCorrection)
  invalidProjectDoesNotStartWork request refused rewrite refused = refl

  Goal : Request → Store.World → Store.World → Result → Set
  Goal request initial final (needsInput actual diagnostic) = actual ≡ request × diagnostic ≡ projectCorrection × admitted actual ≡ false × final ≡ initial
  Goal request initial final (contextResult source outputValue) = admitted request ≡ true ×
    Base.Goal (query request) initial final source × outputValue ≡ answer request (snapshotOf source) (preparationOf source)

  interruptedUnchanged : ∀ request initial final → X.Interrupted (script request) initial final → final ≡ initial
  interruptedUnchanged request initial final (X.atPrefix _ _ _ _ physical) = Base.changesUnchanged physical
  interruptedUnchanged request initial final (X.beforeReply _ effect _ middle reply _ _ previous current) =
    trans (Base.atomicUnchanged middle effect reply final current) (Base.changesUnchanged previous)

  branchCorrect : Base.Operation → ∀ request allowed → admitted request ≡ allowed →
    ∀ initial final result events → E.Runs (branch request allowed) events result →
    X.Changes initial events final → Goal request initial final result
  branchCorrect certificate request false selected initial .initial .(needsInput request projectCorrection) .[]
    (E.returned _) (X.unchanged .initial) = refl , refl , selected , refl
  branchCorrect certificate request true selected initial final result events execution physical =
    let source , run , same = unmapRun (attach request) (Base.script (query request)) events result execution
    in subst (Goal request initial final) (sym same)
      (selected , Base.Operation.recovers certificate (query request) initial initial final source
        (X.atPrefix [] (Base.script (query request)) initial (E.stopped _) (X.unchanged initial))
        (X.completed events run physical) , refl)

  completedCorrect : Base.Operation → ∀ request initial final result →
    X.Completed (script request) initial final result → Goal request initial final result
  completedCorrect certificate request initial final result (X.completed events execution physical) =
    branchCorrect certificate request (admitted request) refl initial final result events execution physical

  correctionCertifiesNoBusinessChanges : Base.Operation → ∀ request initial final actual diagnostic →
    X.Completed (script request) initial final (needsInput actual diagnostic) → Correction.Certified Store.World initial final
  correctionCertifiesNoBusinessChanges certificate request initial final actual diagnostic execution =
    Correction.certified diagnostic (proj₂ (proj₂ (proj₂
      (completedCorrect certificate request initial final (needsInput actual diagnostic) execution))))

  converges : Base.Operation → ∀ request initial interrupted final result →
    X.Interrupted (script request) initial interrupted → X.Completed (script request) interrupted final result →
    Goal request initial final result
  converges certificate request initial interrupted final result interruption execution =
    subst (λ original → Goal request original final result) (interruptedUnchanged request initial interrupted interruption)
      (completedCorrect certificate request interrupted final result execution)

  branchProgress : Base.Operation → ∀ request allowed initial → Σ Store.World (λ final → Σ Result (λ result →
    X.Completed (branch request allowed) initial final result))
  branchProgress certificate request false initial = initial , needsInput request projectCorrection ,
    X.completed [] (E.returned _) (X.unchanged initial)
  branchProgress certificate request true initial =
    let final , source , execution = Base.Operation.progresses certificate (query request) initial
        events = X.Completed.events execution
    in final , attach request source , X.completed events
      (mapRun (attach request) (Base.script (query request)) events source (X.Completed.returned execution))
      (X.Completed.changes execution)

  progress : Base.Operation → ∀ request initial → Σ Store.World (λ final → Σ Result (λ result →
    X.Completed (script request) initial final result))
  progress certificate request initial = branchProgress certificate request (admitted request) initial

  transcript : Result → List E.Event
  transcript (needsInput request diagnostic) = []
  transcript (contextResult source outputValue) = Base.transcript source

  branchObserved : Base.Operation → ∀ request allowed initial final result events →
    E.Runs (branch request allowed) events result → X.Changes initial events final → events ≡ transcript result
  branchObserved certificate request false initial .initial .(needsInput request projectCorrection) .[]
    (E.returned _) (X.unchanged .initial) = refl
  branchObserved certificate request true initial final result events execution physical =
    let source , run , same = unmapRun (attach request) (Base.script (query request)) events result execution
    in trans (Base.Operation.observes certificate (query request) initial final source (X.completed events run physical))
      (sym (cong transcript same))

  observes : Base.Operation → ∀ request initial final result (execution : X.Completed (script request) initial final result) →
    X.Completed.events execution ≡ transcript result
  observes certificate request initial final result (X.completed events execution physical) =
    branchObserved certificate request (admitted request) initial final result events execution physical

  -- Its required field retains the complete retrieval certificate, including
  -- actual receipt binding. Assembly may not replace it with a projection.
  record Operation : Set₁ where
    field retrieval : Base.Operation

  operation : Operation
  operation = record { retrieval = Base.operation }

  toRecoverable : Operation → Recovery.RecoverableFor Store.World Request Result Goal
  toRecoverable certificate = record
    { Effect = Base.Effect
    ; Reply = Base.Reply
    ; script = script
    ; Atomic = Base.Atomic
    ; converges = converges (Operation.retrieval certificate)
    ; progress = progress (Operation.retrieval certificate)
    }

  selectedProceduresUseTheSameStoredWorld : ∀ request snapshot preparation →
    All (Assembly.fromSnapshot (Request.project request) (Store.learningView snapshot))
      (Context.Output.patterns (Assembly.assemble (assembled request snapshot preparation) snapshot))
  selectedProceduresUseTheSameStoredWorld request snapshot preparation =
    Assembly.selectedProceduresUseCurrentSnapshot (assembled request snapshot preparation) snapshot

  assessmentsAreNotTruncated : ∀ request snapshot preparation →
    Learning.Assessments.truncated (Context.Output.assessments (Assembly.assemble (assembled request snapshot preparation) snapshot)) ≡ false
  assessmentsAreNotTruncated request snapshot preparation =
    Assembly.noAssessmentTruncation (assembled request snapshot preparation) snapshot
