{-# OPTIONS --safe #-}
-- The configured query embedding is observed before the document snapshot.
-- Selected passages, ordering and complete parent text come from that world.
module Mimir.PublicDocumentQueryRecovery where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.ConfigurationValues as Config
import Mimir.DocumentQuery as Query
import Mimir.PublicRequest as Public
import Mimir.StorageReadBinding as Database
import Mimir.RetrievalRanking as Ranking
import Mimir.Effects as Effects
import Mimir.Recovery as Recovery

record Request : Set where
  constructor query
  field context : Text; project : Maybe Text; selection : Ranking.Selection

publicRequest : Request → Public.Request
publicRequest request = Public.queryDocument (Request.context request) (Request.project request) (Request.selection request)

allRequestedFieldsArePreserved : ∀ context project selection →
  publicRequest (query context project selection) ≡ Public.queryDocument context project selection
allRequestedFieldsArePreserved context project selection = refl

module Run (database : Database.VectorOperations) (coreConfiguration : Config.Config) where
  configuration : Maybe Config.Embeddings
  configuration = Config.Config.embed coreConfiguration

  -- The old concrete selector receives only this call's observed reply. No
  -- embedding callback is supplied by the dispatcher or the public request.
  module Model response = Database.DocumentReads true (λ _ → response) database

  answer : Request → Store.World → Text ⊎ List Store.Vector → Query.Result
  answer request snapshot response = Model.answer response
    (Model.request (Request.context request) (Request.selection request) (Request.project request)) snapshot

  preparedAnswer : ∀ request snapshot response vector → Query.prepare response ≡ inj₂ vector →
    answer request snapshot response ≡ Query.found
      (Model.passages response snapshot (Model.rows response
        (Model.request (Request.context request) (Request.selection request) (Request.project request)) vector snapshot))
  preparedAnswer request snapshot response vector prepared = cong
    (Database.DocumentReads.preparedAnswer true (λ _ → response) database
      (Model.request (Request.context request) (Request.selection request) (Request.project request)) snapshot) prepared

  data Effect : Set where
    embed : Config.Embeddings → Text → Effect
    readSnapshot : Request → Effect
  Reply : Effect → Set
  Reply (embed _ _) = Text ⊎ List Store.Vector
  Reply (readSnapshot _) = Text ⊎ Store.World
  module E = Effects.Protocol Effect Reply

  data Receipt : Maybe Config.Embeddings → Request → Set where
    notConfigured : ∀ request → Receipt nothing request
    observed : ∀ cfg request → Text ⊎ List Store.Vector → Receipt (just cfg) request

  data DatabaseReceipt : Set where
    notRead : DatabaseReceipt
    failedRead : Text → DatabaseReceipt
    read : Store.World → DatabaseReceipt

  data Result : Set where
    completed : ∀ actualConfiguration request → Receipt actualConfiguration request → DatabaseReceipt → Query.Result → Result

  value : Result → Query.Result
  value (completed _ _ _ _ answer) = answer

  ObservationGoal : ∀ {cfg request} → Receipt cfg request → DatabaseReceipt → Store.World → Query.Result → Set
  ObservationGoal (notConfigured request) notRead initial result = result ≡ Query.preparationRequired Query.notConfigured
  ObservationGoal (notConfigured request) _ initial result = ⊥
  ObservationGoal (observed cfg request response) observedDatabase initial result with Query.prepare response
  ... | inj₁ issue = observedDatabase ≡ notRead × result ≡ Query.preparationRequired issue
  ObservationGoal (observed cfg request response) notRead initial result | inj₂ vector = ⊥
  ObservationGoal (observed cfg request response) (failedRead reason) initial result | inj₂ vector = result ≡ Query.failed reason
  ObservationGoal (observed cfg request response) (read snapshot) initial result | inj₂ vector =
    snapshot ≡ initial × result ≡ answer request snapshot response

  Goal : Request → Store.World → Store.World → Result → Set
  Goal request initial final (completed actualConfiguration actual receipt stored result) =
    actualConfiguration ≡ configuration × actual ≡ request × final ≡ initial × ObservationGoal receipt stored initial result

  afterRead : Config.Embeddings → Request → Text ⊎ List Store.Vector → Text ⊎ Store.World → E.Script Result
  afterRead cfg request response (inj₁ reason) = E.done (completed (just cfg) request (observed cfg request response)
    (failedRead reason) (Query.failed reason))
  afterRead cfg request response (inj₂ snapshot) = E.done (completed (just cfg) request (observed cfg request response)
    (read snapshot) (answer request snapshot response))

  afterEmbedding : Config.Embeddings → Request → Text ⊎ List Store.Vector → E.Script Result
  afterEmbedding cfg request response with Query.prepare response
  ... | inj₁ issue = E.done (completed (just cfg) request (observed cfg request response) notRead (Query.preparationRequired issue))
  ... | inj₂ vector = E.ask (readSnapshot request) (afterRead cfg request response)

  script : Request → E.Script Result
  script request with configuration
  ... | nothing = E.done (completed nothing request (notConfigured request) notRead (Query.preparationRequired Query.notConfigured))
  ... | just cfg = E.ask (embed cfg (Request.context request)) (afterEmbedding cfg request)

  Atomic : Store.World → (effect : Effect) → Reply effect → Store.World → Set
  Atomic before (embed _ _) reply after = after ≡ before
  Atomic before (readSnapshot request) (inj₁ reason) after = after ≡ before
  Atomic before (readSnapshot request) (inj₂ snapshot) after = snapshot ≡ before × after ≡ before
  module X = Recovery.Execution Store.World Effect Reply Atomic

  atomicUnchanged : ∀ before effect reply after → Atomic before effect reply after → after ≡ before
  atomicUnchanged before (embed cfg context) reply after physical = physical
  atomicUnchanged before (readSnapshot request) (inj₁ reason) after physical = physical
  atomicUnchanged before (readSnapshot request) (inj₂ snapshot) after physical = proj₂ physical

  changesUnchanged : ∀ {before events after} → X.Changes before events after → after ≡ before
  changesUnchanged (X.unchanged _) = refl
  changesUnchanged (X.changed before effect reply middle physical later) =
    trans (changesUnchanged later) (atomicUnchanged before effect reply middle physical)

  interruptedUnchanged : ∀ request initial final → X.Interrupted (script request) initial final → final ≡ initial
  interruptedUnchanged request initial final (X.atPrefix _ _ _ _ physical) = changesUnchanged physical
  interruptedUnchanged request initial final (X.beforeReply _ effect _ middle reply _ _ previous active) =
    trans (atomicUnchanged middle effect reply final active) (changesUnchanged previous)

  readCorrect : ∀ cfg → just cfg ≡ configuration → ∀ request response vector → Query.prepare response ≡ inj₂ vector →
    ∀ initial final result events → E.Runs (E.ask (readSnapshot request) (afterRead cfg request response)) events result →
    X.Changes initial events final → Goal request initial final result
  readCorrect cfg configured request response vector prepared initial .initial ._ ._
    (E.replied _ _ (inj₁ reason) (E.returned _)) (X.changed _ _ _ .initial refl (X.unchanged _))
    rewrite prepared = configured , refl , refl , refl
  readCorrect cfg configured request response vector prepared initial .initial ._ ._
    (E.replied _ _ (inj₂ .initial) (E.returned _)) (X.changed _ _ _ .initial (refl , refl) (X.unchanged _))
    rewrite prepared = configured , refl , refl , refl , sym (preparedAnswer request initial response vector prepared)

  embeddingCorrect : ∀ cfg → just cfg ≡ configuration → ∀ request response initial final result events →
    E.Runs (afterEmbedding cfg request response) events result → X.Changes initial events final → Goal request initial final result
  embeddingCorrect cfg configured request response initial final result events execution physical with Query.prepare response in prepared
  ... | inj₁ issue with execution | physical
  ... | E.returned _ | X.unchanged _ rewrite prepared = configured , refl , refl , refl , refl
  embeddingCorrect cfg configured request response initial final result events execution physical | inj₂ vector =
    readCorrect cfg configured request response vector prepared initial final result events execution physical

  completedCorrect : ∀ request initial final result → X.Completed (script request) initial final result → Goal request initial final result
  completedCorrect request initial final result completion with configuration in configured
  ... | nothing with completion
  ... | X.completed .[] (E.returned _) (X.unchanged _) = sym configured , refl , refl , refl
  completedCorrect request initial final result
    (X.completed _ (E.replied _ _ response execution) (X.changed _ _ _ .initial refl physical)) | just cfg =
    embeddingCorrect cfg (sym configured) request response initial final result _ execution physical

  converges : ∀ request initial interrupted final result → X.Interrupted (script request) initial interrupted →
    X.Completed (script request) interrupted final result → Goal request initial final result
  converges request initial interrupted final result crash completion = subst
    (λ before → Goal request before final result) (interruptedUnchanged request initial interrupted crash)
    (completedCorrect request interrupted final result completion)

  progress : ∀ request initial → Σ Store.World (λ final → Σ Result (λ result → X.Completed (script request) initial final result))
  progress request initial with configuration
  ... | nothing = initial , _ , X.completed [] (E.returned _) (X.unchanged _)
  ... | just cfg = initial , _ , X.completed ((embed cfg (Request.context request) , inj₁ []) ∷ [])
    (E.replied _ _ (inj₁ []) (E.returned _)) (X.changed _ _ _ initial refl (X.unchanged _))

  databaseEvents : Request → DatabaseReceipt → List E.Event
  databaseEvents request notRead = []
  databaseEvents request (failedRead reason) = (readSnapshot request , inj₁ reason) ∷ []
  databaseEvents request (read snapshot) = (readSnapshot request , inj₂ snapshot) ∷ []

  transcript : Result → List E.Event
  transcript (completed _ request (notConfigured _) stored result) = []
  transcript (completed _ request (observed cfg _ response) stored result) =
    (embed cfg (Request.context request) , response) ∷ databaseEvents request stored

  embeddingTranscript : ∀ cfg request response result events → E.Runs (afterEmbedding cfg request response) events result →
    (embed cfg (Request.context request) , response) ∷ events ≡ transcript result
  embeddingTranscript cfg request response result events execution with Query.prepare response
  ... | inj₁ issue with execution
  ... | E.returned _ = refl
  embeddingTranscript cfg request response ._ ._ (E.replied _ _ (inj₁ reason) (E.returned _)) | inj₂ vector = refl
  embeddingTranscript cfg request response ._ ._ (E.replied _ _ (inj₂ snapshot) (E.returned _)) | inj₂ vector = refl

  actualReceipts : ∀ request initial final result (execution : X.Completed (script request) initial final result) →
    X.Completed.events execution ≡ transcript result
  actualReceipts request initial final result completion with configuration
  ... | nothing with completion
  ... | X.completed .[] (E.returned _) physical = refl
  actualReceipts request initial final result (X.completed _ (E.replied _ _ response execution) physical) | just cfg =
    embeddingTranscript cfg request response result _ execution

  record Operation : Set₁ where
    field
      recovers : ∀ request initial interrupted final result → X.Interrupted (script request) initial interrupted →
        X.Completed (script request) interrupted final result → Goal request initial final result
      progresses : ∀ request initial → Σ Store.World (λ final → Σ Result (λ result → X.Completed (script request) initial final result))
      observes : ∀ request initial final result (execution : X.Completed (script request) initial final result) →
        X.Completed.events execution ≡ transcript result

  fullOperation : Operation
  fullOperation = record { recovers = converges; progresses = progress; observes = actualReceipts }

  toRecoverable : Operation → Recovery.RecoverableFor Store.World Request Result Goal
  toRecoverable certificate = record
    { Effect = Effect; Reply = Reply; script = script; Atomic = Atomic
    ; converges = Operation.recovers certificate; progress = Operation.progresses certificate }
