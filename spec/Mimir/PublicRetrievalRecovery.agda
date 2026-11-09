{-# OPTIONS --safe #-}
-- Public input never contains an expected embedding or response. The backend
-- response is observed only at the configured backend's exact query effect.
module Mimir.PublicRetrievalRecovery where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; trans; cong)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.CandidateGraph as Graph
import Mimir.EvidenceRead as Evidence
import Mimir.StorageSemantics as Semantics
import Mimir.ConfigurationValues as Config
import Mimir.OrderedRetrieval as Ordered
import Mimir.PreparedRetrieval as Prepared
import Mimir.RetrievalRanking as Ranking
import Mimir.RetrievalProtocol as Retrieval
import Mimir.StorageReadBinding as Database
import Mimir.Effects as Effects
import Mimir.Recovery as Recovery
import Mimir.PublicRequest as Public
import Mimir.LearningCandidates as Candidates

record Request : Set where
  constructor query
  field search : Ordered.Request; includeEvidence : Bool; perBelief : Ranking.Selection

fromFields : Text → Ranking.Selection → Maybe Text → Maybe Candidates.Memory → Bool → Ranking.Selection → Request
fromFields context selection project preference includeEvidence perBelief =
  query (Ordered.searchRequest context project selection preference) includeEvidence perBelief

publicRequest : Request → Public.Request
publicRequest request = Public.relevant (Ordered.Request.context search) (Ordered.Request.selection search)
  (Ordered.Request.project search) (Ordered.Request.preference search) (Request.includeEvidence request) (Request.perBelief request)
  where search = Request.search request

everyRequestedFieldIsPreserved : ∀ context selection project preference includeEvidence perBelief →
  publicRequest (fromFields context selection project preference includeEvidence perBelief) ≡
    Public.relevant context selection project preference includeEvidence perBelief
everyRequestedFieldIsPreserved context selection project preference includeEvidence perBelief = refl

data Response : Set where
  plain : Retrieval.Report → Response
  grounded : Retrieval.Coverage → List Evidence.Grounded → Response

supportingPassages : Store.World → List Store.Ground → List Evidence.Reference
supportingPassages snapshot [] = []
supportingPassages snapshot (edge ∷ rest) with Store.chunk (Store.Ground.chunk edge) (Store.World.chunks snapshot)
... | nothing = supportingPassages snapshot rest
... | just chunk = Evidence.referenceOf (Store.Ground.weight edge) chunk ∷ supportingPassages snapshot rest

groundedBeliefs : Ranking.Selection → Store.World → List Graph.BeliefValues → List Evidence.Grounded
groundedBeliefs selection snapshot [] = []
groundedBeliefs selection snapshot (belief ∷ rest) = Evidence.grounded belief
  (supportingPassages snapshot (Evidence.rankedStable (Graph.BeliefValues.identity belief) selection (Semantics.groundRows snapshot)))
  (Store.sourcesFor (Graph.BeliefValues.identity belief) snapshot) ∷
  groundedBeliefs selection snapshot rest

enrichmentPreservesBeliefsAndOrder : ∀ selection snapshot beliefs →
  map Evidence.Grounded.belief (groundedBeliefs selection snapshot beliefs) ≡ beliefs
enrichmentPreservesBeliefsAndOrder selection snapshot [] = refl
enrichmentPreservesBeliefsAndOrder selection snapshot (belief ∷ rest) =
  cong (belief ∷_) (enrichmentPreservesBeliefsAndOrder selection snapshot rest)

module Run (arithmetic : Ranking.F32) (unicode : Ranking.Unicode)
  (database : Database.VectorOperations) (coreConfiguration : Config.Config) where
  configuration : Maybe Config.Embeddings
  configuration = Config.Config.embed coreConfiguration
  module I = Ordered.Intent arithmetic unicode database
  module P = Prepared.Intent arithmetic unicode database

  candidates : Request → Store.World → List Graph.BeliefValues
  candidates request snapshotState = P.candidates (I.input (Request.search request) Prepared.unconfigured) snapshotState

  answer : Request → Store.World → Prepared.Preparation → Response
  answer request snapshot preparation with Request.includeEvidence request
  ... | false = plain (I.answer (Request.search request) snapshot preparation)
  ... | true = grounded (Retrieval.Report.retrieval retrieved)
      (groundedBeliefs (Request.perBelief request) snapshot (Retrieval.Report.beliefs retrieved))
    where retrieved = I.answer (Request.search request) snapshot preparation

  -- The complete business snapshot is the shared read-only database boundary;
  -- individual SQL replies must retain their existing same-snapshot meanings.
  data Effect : Set where
    readSnapshot : Request → Effect
    embed : Config.Embeddings → Text → Effect

  Reply : Effect → Set
  Reply (readSnapshot request) = Store.World
  Reply (embed backend context) = Text ⊎ List Store.Vector

  module E = Effects.Protocol Effect Reply

  data Receipt : Maybe Config.Embeddings → Request → Store.World → Set where
    noCandidates : ∀ configuration request snapshot → candidates request snapshot ≡ [] →
      Receipt configuration request snapshot
    notConfigured : ∀ request snapshot → Receipt nothing request snapshot
    observed : ∀ backend request snapshot → Text ⊎ List Store.Vector →
      Receipt (just backend) request snapshot

  preparation : ∀ {configuration request snapshot} → Receipt configuration request snapshot → Prepared.Preparation
  preparation (noCandidates _ _ _ _) = Prepared.unconfigured
  preparation (notConfigured _ _) = Prepared.unconfigured
  preparation (observed _ _ _ reply) = Prepared.observed reply

  -- Receipts stay in the semantic result for checking. The public response is
  -- its response, including the factual semantic-availability explanation.
  data Result : Set where
    completed : ∀ actualConfiguration request snapshot → Receipt actualConfiguration request snapshot → Response → Result

  Goal : Request → Store.World → Store.World → Result → Set
  Goal request initial final (completed actualConfiguration actual snapshot receipt response) =
    actualConfiguration ≡ configuration × actual ≡ request × snapshot ≡ initial × final ≡ initial ×
    response ≡ answer actual snapshot (preparation receipt)

  afterCandidates : ∀ request snapshot found → candidates request snapshot ≡ found → E.Script Result
  afterCandidates request snapshot [] available = E.done (completed configuration request snapshot
      (noCandidates configuration request snapshot available)
      (answer request snapshot Prepared.unconfigured))
  afterCandidates request snapshot (_ ∷ _) available with configuration
  ... | nothing = E.done (completed nothing request snapshot (notConfigured request snapshot)
      (answer request snapshot Prepared.unconfigured))
  ... | just backend = E.ask (embed backend (Ordered.Request.context (Request.search request))) (λ reply →
      E.done (completed (just backend) request snapshot (observed backend request snapshot reply)
        (answer request snapshot (Prepared.observed reply))))

  afterSnapshot : Request → Store.World → E.Script Result
  afterSnapshot request snapshot = afterCandidates request snapshot (candidates request snapshot) refl

  script : Request → E.Script Result
  script request = E.ask (readSnapshot request) (afterSnapshot request)

  Atomic : Store.World → (effect : Effect) → Reply effect → Store.World → Set
  Atomic before (readSnapshot request) snapshot after = snapshot ≡ before × after ≡ before
  Atomic before (embed backend context) reply after = after ≡ before

  module X = Recovery.Execution Store.World Effect Reply Atomic

  atomicUnchanged : ∀ before effect reply after → Atomic before effect reply after → after ≡ before
  atomicUnchanged before (readSnapshot request) snapshot after proof = proj₂ proof
  atomicUnchanged before (embed backend context) reply after proof = proof

  changesUnchanged : ∀ {before events after} → X.Changes before events after → after ≡ before
  changesUnchanged (X.unchanged _) = refl
  changesUnchanged (X.changed before effect reply middle physical later) =
    trans (changesUnchanged later) (atomicUnchanged before effect reply middle physical)

  interruptedUnchanged : ∀ request initial final → X.Interrupted (script request) initial final → final ≡ initial
  interruptedUnchanged request initial final (X.atPrefix _ _ _ _ physical) = changesUnchanged physical
  interruptedUnchanged request initial final (X.beforeReply _ effect _ middle reply _ _ previous current) =
    trans (atomicUnchanged middle effect reply final current) (changesUnchanged previous)

  terminalCorrect : ∀ actualConfiguration → actualConfiguration ≡ configuration →
    ∀ request snapshot (receipt : Receipt actualConfiguration request snapshot) final result events →
    E.Runs (E.done (completed actualConfiguration request snapshot receipt (answer request snapshot (preparation receipt)))) events result →
    X.Changes snapshot events final → Goal request snapshot final result
  terminalCorrect actualConfiguration configured request snapshot receipt .snapshot ._ .[] (E.returned _) (X.unchanged .snapshot) =
    configured , refl , refl , refl , refl

  embeddingCorrect : ∀ backend → just backend ≡ configuration → ∀ request snapshot final result events →
    E.Runs (E.ask (embed backend (Ordered.Request.context (Request.search request))) (λ reply →
      E.done (completed (just backend) request snapshot (observed backend request snapshot reply)
        (answer request snapshot (Prepared.observed reply))))) events result →
    X.Changes snapshot events final → Goal request snapshot final result
  embeddingCorrect backend configured request snapshot .snapshot ._ ._
    (E.replied _ _ reply (E.returned _))
    (X.changed .snapshot _ .reply .snapshot refl (X.unchanged .snapshot)) =
    configured , refl , refl , refl , refl

  afterCandidatesCorrect : ∀ request snapshot found available final result events →
    E.Runs (afterCandidates request snapshot found available) events result →
    X.Changes snapshot events final → Goal request snapshot final result
  afterCandidatesCorrect request snapshot [] available final result events execution physical =
    terminalCorrect configuration refl request snapshot (noCandidates configuration request snapshot available)
      final result events execution physical
  afterCandidatesCorrect request snapshot (_ ∷ _) available final result events execution physical
    with configuration in configured
  ... | nothing = terminalCorrect nothing (Relation.Binary.PropositionalEquality.sym configured)
      request snapshot (notConfigured request snapshot) final result events execution physical
  ... | just backend = embeddingCorrect backend (Relation.Binary.PropositionalEquality.sym configured)
      request snapshot final result events execution physical

  afterSnapshotCorrect : ∀ request snapshot final result events →
    E.Runs (afterSnapshot request snapshot) events result →
    X.Changes snapshot events final → Goal request snapshot final result
  afterSnapshotCorrect request snapshot = afterCandidatesCorrect request snapshot (candidates request snapshot) refl

  completedCorrect : ∀ request initial final result →
    X.Completed (script request) initial final result → Goal request initial final result
  completedCorrect request initial final result
    (X.completed _ (E.replied _ _ snapshot execution)
      (X.changed .initial _ .snapshot .initial (refl , refl) physical)) =
    afterSnapshotCorrect request initial final result _ execution physical

  converges : ∀ request initial interrupted final result →
    X.Interrupted (script request) initial interrupted → X.Completed (script request) interrupted final result →
    Goal request initial final result
  converges request initial interrupted final result interruption execution =
    subst (λ original → Goal request original final result)
      (interruptedUnchanged request initial interrupted interruption)
      (completedCorrect request interrupted final result execution)

  returned : ∀ snapshot (result : Result) → X.Completed (E.done result) snapshot snapshot result
  returned snapshot result = X.completed [] (E.returned result) (X.unchanged snapshot)

  embeddingProgress : ∀ backend request snapshot → Σ Result (λ result →
    X.Completed (E.ask (embed backend (Ordered.Request.context (Request.search request))) (λ reply →
      E.done (completed (just backend) request snapshot (observed backend request snapshot reply)
        (answer request snapshot (Prepared.observed reply))))) snapshot snapshot result)
  embeddingProgress backend request snapshot = response , X.completed
    ((embed backend (Ordered.Request.context (Request.search request)) , reply) ∷ [])
    (E.replied _ _ reply (E.returned response))
    (X.changed snapshot _ reply snapshot refl (X.unchanged snapshot))
    where
    -- Progress is existence of an allowed external outcome, not a guarantee
    -- that a provider responds, succeeds, or returns the same reply on retry.
    reply : Text ⊎ List Store.Vector
    reply = inj₁ []
    response = completed (just backend) request snapshot (observed backend request snapshot reply)
      (answer request snapshot (Prepared.observed reply))

  afterCandidatesProgress : ∀ request snapshot found available →
    Σ Result (λ result → X.Completed (afterCandidates request snapshot found available) snapshot snapshot result)
  afterCandidatesProgress request snapshot [] available = response , returned snapshot response
    where response = completed configuration request snapshot (noCandidates configuration request snapshot available)
            (answer request snapshot Prepared.unconfigured)
  afterCandidatesProgress request snapshot (_ ∷ _) available with configuration
  ... | nothing = response , returned snapshot response
    where response = completed nothing request snapshot (notConfigured request snapshot)
            (answer request snapshot Prepared.unconfigured)
  ... | just backend = embeddingProgress backend request snapshot

  progress : ∀ request initial → Σ Store.World (λ final → Σ Result (λ result →
    X.Completed (script request) initial final result))
  progress request initial with afterCandidatesProgress request initial (candidates request initial) refl
  ... | result , X.completed events execution physical = initial , result , X.completed
    ((readSnapshot request , initial) ∷ events)
    (E.replied (readSnapshot request) (afterSnapshot request) initial execution)
    (X.changed initial (readSnapshot request) initial initial (refl , refl) physical)

  receiptEvents : ∀ {configuration request snapshot} → Receipt configuration request snapshot → List E.Event
  receiptEvents (noCandidates _ _ _ _) = []
  receiptEvents (notConfigured _ _) = []
  receiptEvents (observed backend request snapshot reply) =
    (embed backend (Ordered.Request.context (Request.search request)) , reply) ∷ []

  transcript : Result → List E.Event
  transcript (completed configuration request snapshot receipt response) =
    (readSnapshot request , snapshot) ∷ receiptEvents receipt

  terminalTranscript : ∀ actualConfiguration request snapshot receipt → receiptEvents receipt ≡ [] → ∀ result events →
    E.Runs (E.done (completed actualConfiguration request snapshot receipt
      (answer request snapshot (preparation receipt)))) events result →
    (readSnapshot request , snapshot) ∷ events ≡ transcript result
  terminalTranscript actualConfiguration request snapshot receipt empty ._ .[] (E.returned _) =
    Relation.Binary.PropositionalEquality.cong ((readSnapshot request , snapshot) ∷_)
      (Relation.Binary.PropositionalEquality.sym empty)

  embeddingTranscript : ∀ backend request snapshot result events →
    E.Runs (E.ask (embed backend (Ordered.Request.context (Request.search request))) (λ reply →
      E.done (completed (just backend) request snapshot (observed backend request snapshot reply)
        (answer request snapshot (Prepared.observed reply))))) events result →
    (readSnapshot request , snapshot) ∷ events ≡ transcript result
  embeddingTranscript backend request snapshot ._ ._ (E.replied _ _ reply (E.returned _)) = refl

  afterCandidatesTranscript : ∀ request snapshot found available result events →
    E.Runs (afterCandidates request snapshot found available) events result →
    (readSnapshot request , snapshot) ∷ events ≡ transcript result
  afterCandidatesTranscript request snapshot [] available result events execution =
    terminalTranscript configuration request snapshot (noCandidates configuration request snapshot available) refl result events execution
  afterCandidatesTranscript request snapshot (_ ∷ _) available result events execution with configuration
  ... | nothing = terminalTranscript nothing request snapshot (notConfigured request snapshot) refl result events execution
  ... | just backend = embeddingTranscript backend request snapshot result events execution

  -- The semantic receipt is exactly the execution's observed transcript.
  -- In particular, a vector cannot come from another query or backend, or
  -- appear as a caller-supplied preparation argument.
  actualReceipts : ∀ request initial final result (execution : X.Completed (script request) initial final result) →
    X.Completed.events execution ≡ transcript result
  actualReceipts request initial final result (X.completed _ (E.replied _ _ snapshot execution) physical) =
    afterCandidatesTranscript request snapshot (candidates request snapshot) refl result _ execution

  -- The dispatcher must receive this certificate, not just the recoverability
  -- projection: external observations are a required registration obligation.
  record Operation : Set₁ where
    field
      recovers : ∀ request initial interrupted final result →
        X.Interrupted (script request) initial interrupted → X.Completed (script request) interrupted final result →
        Goal request initial final result
      progresses : ∀ request initial → Σ Store.World (λ final → Σ Result (λ result →
        X.Completed (script request) initial final result))
      observes : ∀ request initial final result (execution : X.Completed (script request) initial final result) →
        X.Completed.events execution ≡ transcript result

  operation : Operation
  operation = record { recovers = converges; progresses = progress; observes = actualReceipts }

  toRecoverable : Operation → Recovery.RecoverableFor Store.World Request Result Goal
  toRecoverable certificate = record
    { Effect = Effect
    ; Reply = Reply
    ; script = script
    ; Atomic = Atomic
    ; converges = Operation.recovers certificate
    ; progress = Operation.progresses certificate
    }
