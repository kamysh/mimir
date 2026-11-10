{-# OPTIONS --safe #-}
-- A durable defeat edge survives a later request for a numerical decision.
-- Retries reuse the original answers at both independently committed phases.
module Mimir.DefeatRecovery where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (true; false)
open import Data.Float.Base using (Float)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.Binary64 as Binary
import Mimir.DatabaseTransaction as DB
import Mimir.GraphMutationProtocol as Mutation
import Mimir.GraphWrites as Writes
import Mimir.GroundingRecovery as Ground
import Mimir.InferenceStorageBinding as Inference
import Mimir.PosteriorComputation as P
import Mimir.PublicRequest as Public
import Mimir.RecordDecoding as Decode
import Mimir.RecoverableStoreSequence as Sequence
import Mimir.RecoverableStoreStep as Step
import Mimir.RegisteredStoreAdmission as Admission
import Mimir.RetrievalRanking as Ranking
import Mimir.ReviewSchema as Review
import Mimir.StandardLibrary as Conversion
import Mimir.StructuredValue as Wire
import Mimir.ToolCatalog as Tools
import Mimir.Validation as Validation
import Mimir.ApplicationFloat as FloatValue
import Mimir.GraphNumerics as Numbers

record Request : Set where
  constructor request
  field from to : ℕ; weight : Binary.Number

answer = Ground.answer

firstKey secondKey : ℕ → Text
firstKey _ = toList "[\"store.insert_edge\",null]"
secondKey _ = toList "[\"store.propagate_locked\",null]"

firstDistinct : ∀ token → firstKey token ≡ Step.resultKey → ⊥
firstDistinct token ()
secondDistinct : ∀ token → secondKey token ≡ Step.resultKey → ⊥
secondDistinct token ()
keysDifferent : ∀ token → firstKey token ≡ secondKey token → ⊥
keysDifferent token ()

module Business (received : ℤ) (databaseSum : List Float → Float) (calculator : P.Calculator) where
  module G = Ground.Business databaseSum calculator
  module N = Inference.NumericalOutcome databaseSum
  open G using (Diagnostic; requestFault; preparation)
  Outcome = G.Outcome

  weightFault : Validation.Fault
  weightFault = Validation.fault (Validation.key "weight" ∷ []) Validation.invalidNumber
    "Supply a finite defeat weight between 0 and 1 inclusive. Correct the original weight; do not clamp it or guess a replacement."

  endpointFault : ℕ → Store.World → Validation.Fault
  endpointFault from before with Ranking.lookup from (Store.beliefs before)
  ... | nothing = Validation.fault (Validation.key "from_id" ∷ []) Validation.missingReference
    "The defeat source belief is not stored. Use list_beliefs or query_relevant to find the intended source. If its identity is unknown, ask the user; do not invent an identifier."
  ... | just _ = Validation.fault (Validation.key "to_id" ∷ []) Validation.missingReference
    "The defeat target belief is not stored. Use list_beliefs or query_relevant to find the intended target. If its identity is unknown, ask the user; do not invent an identifier."

  clockFault : Validation.Fault
  clockFault = Validation.fault (Validation.key "database" ∷ Validation.key "retirement" ∷ []) Validation.malformedInput
    "An existing defeated target has no first defeat date or explicit legacy-expired marker. Read its stored metadata and migration receipt, then open the user dialog. Do not invent a date, restart grace or classify new broken data as legacy."

  edge : Request → Store.World → Outcome
  edge (request from to weight) before with Writes.insertEdge received from to Review.defeats weight before
  ... | Writes.invalidWeight = inj₁ (requestFault weightFault)
  ... | Writes.missingEndpoint = inj₁ (requestFault (endpointFault from before))
  ... | Writes.invalidRetirement = inj₁ (requestFault clockFault)
  ... | Writes.applied after = inj₂ (after , answer)

  -- One requested independent contribution, retaining every other component.
  EdgeGoal : Request → Store.World → Outcome → Set
  EdgeGoal (request from to weight) before outcome with Writes.insertEdge received from to Review.defeats weight before
  ... | Writes.invalidWeight = outcome ≡ inj₁ (requestFault weightFault)
  ... | Writes.missingEndpoint = outcome ≡ inj₁ (requestFault (endpointFault from before))
  ... | Writes.invalidRetirement = outcome ≡ inj₁ (requestFault clockFault)
  ... | Writes.applied after = outcome ≡ inj₂ (after , answer)

  edgeMeaning : ∀ requested before → EdgeGoal requested before (edge requested before)
  edgeMeaning (request from to weight) before with Writes.insertEdge received from to Review.defeats weight before
  ... | Writes.invalidWeight = refl
  ... | Writes.missingEndpoint = refl
  ... | Writes.invalidRetirement = refl
  ... | Writes.applied after = refl

  edgeKeepsJournal : ∀ requested before after reply → edge requested before ≡ inj₂ (after , reply) →
    Store.World.operations after ≡ Store.World.operations before
  edgeKeepsJournal (request from to weight) before after reply accepted
    with Writes.insertEdge received from to Review.defeats weight before in inserted
  ... | Writes.invalidWeight with accepted
  ... | ()
  edgeKeepsJournal (request from to weight) before after reply accepted | Writes.missingEndpoint with accepted
  ... | ()
  edgeKeepsJournal (request from to weight) before after reply accepted | Writes.invalidRetirement with accepted
  ... | ()
  edgeKeepsJournal (request from to weight) before after reply accepted | Writes.applied changed with accepted
  ... | refl = Writes.insertEdgeKeepsJournal received from to Review.defeats weight before changed inserted

module FinalBusiness (databaseSum : List Float → Float) (calculator : P.Calculator) where
  module G = Ground.Business databaseSum calculator
  module N = Inference.NumericalOutcome databaseSum
  open G using (preparation)
  Outcome = G.Outcome

  FinalGoal : ℤ → Request → Store.World → Outcome → Set
  FinalGoal publicationTime requested before outcome with N.prepare (N.propagate (Request.from requested)) before
  ... | inj₁ issue = outcome ≡ inj₁ (preparation issue)
  ... | inj₂ selected = G.Selected.Goal publicationTime selected before outcome

  checked : ∀ publicationTime requested before → Σ Outcome (FinalGoal publicationTime requested before)
  checked publicationTime requested before with N.prepare (N.propagate (Request.from requested)) before
  ... | inj₁ issue = inj₁ (preparation issue) , refl
  ... | inj₂ selected = G.Selected.checked publicationTime selected before

  finalKeepsJournal : ∀ publicationTime requested before after reply →
    proj₁ (checked publicationTime requested before) ≡ inj₂ (after , reply) →
    Store.World.operations after ≡ Store.World.operations before
  finalKeepsJournal publicationTime requested before after reply accepted
    with N.prepare (N.propagate (Request.from requested)) before
  ... | inj₁ issue with accepted
  ... | ()
  finalKeepsJournal publicationTime requested before after reply accepted | inj₂ selected =
    G.Selected.publicationKeepsJournal publicationTime selected before after reply
      (subst (G.Selected.Goal publicationTime selected before) accepted
        (proj₂ (G.Selected.checked publicationTime selected before)))

module BoundRequest (conversion : Conversion.Contract)
  (databaseSum : List Float → Float) (calculator : P.Calculator) where
  module D = Public.Decode conversion
  module G = Ground.Business databaseSum calculator

  descriptor : Admission.PairDescriptor
  descriptor = Admission.pairDescriptor (toList "record_defeat")
    (toList "store.insert_edge") (firstKey 0)
    (toList "store.propagate_locked") (secondKey 0)

  mismatch : Validation.Fault
  mismatch = Validation.fault [] Validation.malformedInput
    "Use the exact original defeat arguments and empty settings. Read the saved plan and answers; do not replace the request or repeat its edge."

  decode : Wire.Value → Validation.Fault ⊎ Request
  decode raw with D.readBoundTool Tools.recordDefeat raw
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ (Public.mutation (Mutation.edge from to Review.defeats weight)) = inj₂ (request from to weight)
  ... | inj₂ _ = inj₁ mismatch

  original : ℕ → Step.Registration → Validation.Fault ⊎ Request
  original token registration with Admission.resolvePair descriptor token registration
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ (reserved , binding) with Store.BindingRow.settings binding
  ... | Wire.object [] = decode (Store.BindingRow.arguments binding)
  ... | _ = inj₁ mismatch

  admit : ℕ → Step.Registration → Maybe G.Diagnostic
  admit token registration with original token registration
  ... | inj₁ fault = just (G.requestFault fault)
  ... | inj₂ _ = nothing

-- Receipt metadata is an internal argument to one shared kernel. It is
-- supplied by each physical effect, not admitted as a public request field.
module Core (conversion : Conversion.Contract)
  (databaseSum : List Float → Float) (calculator : P.Calculator) where
  module G = Ground.Business databaseSum calculator
  module F = FinalBusiness databaseSum calculator
  module Binding = BoundRequest conversion databaseSum calculator
  Internal = ℕ × ℤ
  admit : Internal → Step.Registration → Maybe G.Diagnostic
  admit input = Binding.admit (proj₁ input)
  edgeDecision : Internal → Store.World → G.Outcome
  edgeDecision (token , received) before with Binding.original token (Step.registration before)
  ... | inj₁ fault = inj₁ (G.requestFault fault)
  ... | inj₂ requested = Business.edge received databaseSum calculator requested before
  edgeJournal : ∀ input before after reply → edgeDecision input before ≡ inj₂ (after , reply) →
    Store.World.operations after ≡ Store.World.operations before
  edgeJournal (token , received) before after reply accepted with Binding.original token (Step.registration before)
  ... | inj₁ fault with accepted
  ... | ()
  edgeJournal (token , received) before after reply accepted | inj₂ requested =
    Business.edgeKeepsJournal received databaseSum calculator requested before after reply accepted
  module Prefix = Sequence.SavedPrefix Internal G.Diagnostic proj₁
    (λ input → firstKey (proj₁ input)) (λ input → secondKey (proj₁ input))
    (λ input → firstDistinct (proj₁ input)) (λ input → keysDifferent (proj₁ input)) edgeDecision edgeJournal admit

  finalDecision : Internal → Store.World → G.Outcome
  finalDecision (token , received) before with Binding.original token (Step.registration before)
  ... | inj₁ fault = inj₁ (G.requestFault fault)
  ... | inj₂ requested = proj₁ (F.checked received requested before)
  finalJournal : ∀ input before after reply → finalDecision input before ≡ inj₂ (after , reply) →
    Store.World.operations after ≡ Store.World.operations before
  finalJournal (token , received) before after reply accepted with Binding.original token (Step.registration before)
  ... | inj₁ fault with accepted
  ... | ()
  finalJournal (token , received) before after reply accepted | inj₂ requested =
    F.finalKeepsJournal received requested before after reply accepted
  module Final = Step.Admitted Internal G.Diagnostic proj₁ (λ input → secondKey (proj₁ input))
    (λ input → secondDistinct (proj₁ input)) finalDecision finalJournal admit
  finalPreservesFirst : ∀ input before →
    Store.lookupSaved (proj₁ (Final.execute input before)) (proj₁ input) (firstKey (proj₁ input)) ≡
      Store.lookupSaved before (proj₁ input) (firstKey (proj₁ input))
  finalPreservesFirst input@(token , received) before with admit input (Step.registration before)
  ... | just _ = refl
  ... | nothing with Store.lookupCancellation before token
  ... | just _ = refl
  ... | nothing with Store.lookupSaved before token (secondKey token) | Store.lookupSaved before token Step.resultKey
  ... | just _ | just _ = refl
  ... | just _ | nothing = refl
  ... | nothing | just _ = refl
  ... | nothing | nothing with finalDecision input before in accepted
  ... | inj₁ _ = refl
  ... | inj₂ (changed , reply) = trans
    (Store.otherSavedAnswerPreserved (Final.Kernel.firstPublication input changed reply) token Step.resultKey reply
      token (firstKey token) (λ same → firstDistinct token (proj₂ same)))
    (trans (Store.otherSavedAnswerPreserved changed token (secondKey token) reply token (firstKey token)
      (λ same → keysDifferent token (proj₂ same)))
      (Final.Kernel.changedLookup input before changed reply (firstKey token) accepted))
  second : Internal → Store.World → Store.World × Final.Reply
  second input@(token , received) before with Store.lookupSaved before token (firstKey token)
  ... | nothing = before , Step.needsRecovery
  ... | just _ = Final.execute input before
  secondStable : ∀ input before → second input (proj₁ (second input before)) ≡ second input before
  secondStable input@(token , received) before with Store.lookupSaved before token (firstKey token) in saved
  ... | nothing rewrite saved = refl
  ... | just _ rewrite finalPreservesFirst input before | saved = Final.stable input before
  secondPhysical : ∀ input before → DB.Atomic before (proj₁ (second input before))
    (Step.receiptFor (proj₂ (second input before))) (proj₁ (second input before))
  secondPhysical input@(token , received) before with Store.lookupSaved before token (firstKey token)
  ... | nothing = DB.abortedNone
  ... | just _ = Final.expectedPhysical input before

module AtStatementTime (received finalReceived : ℤ) (conversion : Conversion.Contract)
  (databaseSum : List Float → Float) (calculator : P.Calculator) where
  module B = Business received databaseSum calculator
  module F = FinalBusiness databaseSum calculator
  module D = Public.Decode conversion
  module G = Ground.Business databaseSum calculator

  open BoundRequest conversion databaseSum calculator public using (descriptor; mismatch; decode; original; admit)

  module C = Core conversion databaseSum calculator
  module Prefix = C.Prefix
  module Final = C.Final
  edgeDecision = λ token → C.edgeDecision (token , received)
  edgeJournal = λ token → C.edgeJournal (token , received)
  finalDecision = λ token → C.finalDecision (token , finalReceived)
  finalJournal = λ token → C.finalJournal (token , finalReceived)
  finalPreservesFirst = λ token → C.finalPreservesFirst (token , finalReceived)
  second = λ token → C.second (token , finalReceived)
  secondStable = λ token → C.secondStable (token , finalReceived)
  secondPhysical = λ token → C.secondPhysical (token , finalReceived)
  prefixExecute = λ token → Prefix.execute (token , received)

  module Run = Sequence.Evaluation ℕ G.Diagnostic prefixExecute second

  publishedFirst : ∀ token before changed reply → finalDecision token before ≡ inj₂ (changed , reply) →
    Store.lookupSaved (Final.Kernel.publication (token , finalReceived) changed reply) token (firstKey token) ≡
      Store.lookupSaved before token (firstKey token)
  publishedFirst token before changed reply accepted = trans
    (Store.otherSavedAnswerPreserved (Final.Kernel.firstPublication (token , finalReceived) changed reply) token Step.resultKey reply
      token (firstKey token) (λ same → firstDistinct token (proj₂ same)))
    (trans (Store.otherSavedAnswerPreserved changed token (secondKey token) reply token (firstKey token)
      (λ same → keysDifferent token (proj₂ same)))
      (Final.Kernel.changedLookup (token , finalReceived) before changed reply (firstKey token) accepted))

  prefixCompleteReplay : ∀ token before saved next result →
    admit token (Step.registration before) ≡ nothing →
    Store.lookupCancellation before token ≡ nothing →
    Store.lookupSaved before token (firstKey token) ≡ just saved →
    Store.lookupSaved before token (secondKey token) ≡ just next →
    Store.lookupSaved before token Step.resultKey ≡ just result →
    prefixExecute token before ≡ (before , Step.done saved)
  prefixCompleteReplay token before saved next result admitted active firstSaved nextSaved resultSaved
    rewrite admitted | active | firstSaved | nextSaved | resultSaved = refl

  prefixPendingReplay : ∀ token before saved →
    admit token (Step.registration before) ≡ nothing →
    Store.lookupCancellation before token ≡ nothing →
    Store.lookupSaved before token (firstKey token) ≡ just saved →
    Store.lookupSaved before token (secondKey token) ≡ nothing →
    Store.lookupSaved before token Step.resultKey ≡ nothing →
    prefixExecute token before ≡ (before , Step.done saved)
  prefixPendingReplay token before saved admitted active firstSaved nextSaved resultSaved
    rewrite admitted | active | firstSaved | nextSaved | resultSaved = refl

  secondCompleteReplay : ∀ token before saved next result →
    admit token (Step.registration before) ≡ nothing →
    Store.lookupCancellation before token ≡ nothing →
    Store.lookupSaved before token (firstKey token) ≡ just saved →
    Store.lookupSaved before token (secondKey token) ≡ just next →
    Store.lookupSaved before token Step.resultKey ≡ just result →
    second token before ≡ (before , Step.done next)
  secondCompleteReplay token before saved next result admitted active firstSaved nextSaved resultSaved
    rewrite firstSaved | admitted | active | nextSaved | resultSaved = refl

  secondFresh : ∀ token before saved changed reply →
    admit token (Step.registration before) ≡ nothing →
    Store.lookupCancellation before token ≡ nothing →
    Store.lookupSaved before token (firstKey token) ≡ just saved →
    Store.lookupSaved before token (secondKey token) ≡ nothing →
    Store.lookupSaved before token Step.resultKey ≡ nothing →
    finalDecision token before ≡ inj₂ (changed , reply) →
    second token before ≡ (Final.Kernel.publication (token , finalReceived) changed reply , Step.done reply)
  secondFresh token before saved changed reply admitted active firstSaved nextSaved resultSaved accepted
    rewrite firstSaved | admitted | active | nextSaved | resultSaved | accepted = refl

  publishedEvaluation : ∀ token before changed reply saved →
    admit token (Step.registration before) ≡ nothing →
    Store.lookupCancellation before token ≡ nothing →
    Store.lookupSaved before token (firstKey token) ≡ just saved →
    Store.lookupSaved before token (secondKey token) ≡ nothing →
    Store.lookupSaved before token Step.resultKey ≡ nothing →
    finalDecision token before ≡ inj₂ (changed , reply) →
    Run.evaluate token (Final.Kernel.publication (token , finalReceived) changed reply) ≡
      (Final.Kernel.publication (token , finalReceived) changed reply , Step.done reply)
  publishedEvaluation token before changed reply saved admitted active firstSaved secondAbsent resultAbsent accepted = trans
    (cong (λ result → Run.remaining token (proj₂ result) (proj₁ result))
      (prefixCompleteReplay token published saved reply reply publicationAdmitted publicationActive
        publicationFirst publicationSecond publicationResult))
    (secondCompleteReplay token published saved reply reply publicationAdmitted publicationActive
      publicationFirst publicationSecond publicationResult)
    where
    published = Final.Kernel.publication (token , finalReceived) changed reply
    publicationAdmitted = trans (cong (admit token)
      (Final.Kernel.publicationKeepsRegistration (token , finalReceived) before changed reply accepted)) admitted
    publicationActive = trans (Final.Kernel.publicationKeepsCancellation (token , finalReceived) before changed reply accepted) active
    publicationFirst = trans (publishedFirst token before changed reply accepted) firstSaved
    publicationSecond = Final.Kernel.publishedStepReadable (token , finalReceived) before changed reply accepted secondAbsent
    publicationResult = Final.Kernel.publishedResultReadable (token , finalReceived) before changed reply accepted resultAbsent

  originalEvaluation : ∀ token before changed reply saved →
    admit token (Step.registration before) ≡ nothing →
    Store.lookupCancellation before token ≡ nothing →
    Store.lookupSaved before token (firstKey token) ≡ just saved →
    Store.lookupSaved before token (secondKey token) ≡ nothing →
    Store.lookupSaved before token Step.resultKey ≡ nothing →
    finalDecision token before ≡ inj₂ (changed , reply) →
    Run.evaluate token before ≡ (Final.Kernel.publication (token , finalReceived) changed reply , Step.done reply)
  originalEvaluation token before changed reply saved admitted active firstSaved secondAbsent resultAbsent accepted = trans
    (cong (λ result → Run.remaining token (proj₂ result) (proj₁ result))
      (prefixPendingReplay token before saved admitted active firstSaved secondAbsent resultAbsent))
    (secondFresh token before saved changed reply admitted active firstSaved secondAbsent resultAbsent accepted)

  EdgeIntent : ℕ → Store.World → B.Outcome → Set
  EdgeIntent token before outcome with original token (Step.registration before)
  ... | inj₁ fault = outcome ≡ inj₁ (G.requestFault fault)
  ... | inj₂ requested = B.EdgeGoal requested before outcome

  edgeDecisionMeaning : ∀ token before → EdgeIntent token before (edgeDecision token before)
  edgeDecisionMeaning token before with original token (Step.registration before)
  ... | inj₁ fault = refl
  ... | inj₂ requested = B.edgeMeaning requested before

  FreshPrefixGoal : ℕ → Store.World → Store.World → Prefix.Reply → Set
  FreshPrefixGoal token before after (Step.done reply) = Σ Store.World (λ changed →
    EdgeIntent token before (inj₂ (changed , reply)) ×
      after ≡ Prefix.Base.firstPublication (token , received) changed reply)
  FreshPrefixGoal token before after (Step.needsInput diagnostic) =
    after ≡ before × EdgeIntent token before (inj₁ diagnostic)
  FreshPrefixGoal token before after _ = ⊥

  freshPrefixMeaning : ∀ token before → FreshPrefixGoal token before
    (proj₁ (Prefix.fresh (token , received) before)) (proj₂ (Prefix.fresh (token , received) before))
  freshPrefixMeaning token before with edgeDecision token before in accepted
  ... | inj₁ diagnostic = refl , subst (EdgeIntent token before) accepted (edgeDecisionMeaning token before)
  ... | inj₂ (changed , reply) = changed ,
    subst (EdgeIntent token before) accepted (edgeDecisionMeaning token before) , refl

  PrefixGoal : ℕ → Store.World → Store.World → Prefix.Reply → Set
  PrefixGoal token before after reply with admit token (Step.registration before)
  ... | just diagnostic = after ≡ before × reply ≡ Step.needsInput diagnostic
  ... | nothing with Store.lookupCancellation before token
  ... | just cancelled = after ≡ before × reply ≡ Step.cancelled cancelled
  ... | nothing with Store.lookupSaved before token (firstKey token)
    | Store.lookupSaved before token (secondKey token) | Store.lookupSaved before token Step.resultKey
  ... | just saved | nothing | nothing = after ≡ before × reply ≡ Step.done saved
  ... | just saved | just _ | just _ = after ≡ before × reply ≡ Step.done saved
  ... | just _ | nothing | just _ = after ≡ before × reply ≡ Step.needsRecovery
  ... | just _ | just _ | nothing = after ≡ before × reply ≡ Step.needsRecovery
  ... | nothing | nothing | just _ = after ≡ before × reply ≡ Step.needsRecovery
  ... | nothing | just _ | nothing = after ≡ before × reply ≡ Step.needsRecovery
  ... | nothing | just _ | just _ = after ≡ before × reply ≡ Step.needsRecovery
  ... | nothing | nothing | nothing = FreshPrefixGoal token before after reply

  prefixMeaning : ∀ token before → PrefixGoal token before
    (proj₁ (prefixExecute token before)) (proj₂ (prefixExecute token before))
  prefixMeaning token before with admit token (Step.registration before)
  ... | just diagnostic = refl , refl
  ... | nothing with Store.lookupCancellation before token
  ... | just cancelled = refl , refl
  ... | nothing with Store.lookupSaved before token (firstKey token)
    | Store.lookupSaved before token (secondKey token) | Store.lookupSaved before token Step.resultKey
  ... | just _ | nothing | nothing = refl , refl
  ... | just _ | just _ | just _ = refl , refl
  ... | just _ | nothing | just _ = refl , refl
  ... | just _ | just _ | nothing = refl , refl
  ... | nothing | nothing | just _ = refl , refl
  ... | nothing | just _ | nothing = refl , refl
  ... | nothing | just _ | just _ = refl , refl
  ... | nothing | nothing | nothing = freshPrefixMeaning token before

  FinalIntent : ℕ → Store.World → B.Outcome → Set
  FinalIntent token before outcome with original token (Step.registration before)
  ... | inj₁ fault = outcome ≡ inj₁ (G.requestFault fault)
  ... | inj₂ requested = F.FinalGoal finalReceived requested before outcome

  finalDecisionMeaning : ∀ token before → FinalIntent token before (finalDecision token before)
  finalDecisionMeaning token before with original token (Step.registration before)
  ... | inj₁ fault = refl
  ... | inj₂ requested = proj₂ (F.checked finalReceived requested before)

  FreshFinalGoal : ℕ → Store.World → Store.World → Final.Reply → Set
  FreshFinalGoal token before after (Step.done reply) = Σ Store.World (λ changed →
    FinalIntent token before (inj₂ (changed , reply)) ×
      after ≡ Final.Kernel.publication (token , finalReceived) changed reply)
  FreshFinalGoal token before after (Step.needsInput diagnostic) =
    after ≡ before × FinalIntent token before (inj₁ diagnostic)
  FreshFinalGoal token before after _ = ⊥

  freshFinalMeaning : ∀ token before → FreshFinalGoal token before
    (proj₁ (Final.Kernel.fresh (token , finalReceived) before)) (proj₂ (Final.Kernel.fresh (token , finalReceived) before))
  freshFinalMeaning token before with finalDecision token before in accepted
  ... | inj₁ diagnostic = refl , subst (FinalIntent token before) accepted (finalDecisionMeaning token before)
  ... | inj₂ (changed , reply) = changed ,
    subst (FinalIntent token before) accepted (finalDecisionMeaning token before) , refl

  FinalGoal : ℕ → Store.World → Store.World → Final.Reply → Set
  FinalGoal token before after reply with Store.lookupSaved before token (firstKey token)
  ... | nothing = after ≡ before × reply ≡ Step.needsRecovery
  ... | just _ with admit token (Step.registration before)
  ... | just diagnostic = after ≡ before × reply ≡ Step.needsInput diagnostic
  ... | nothing with Store.lookupCancellation before token
  ... | just cancelled = after ≡ before × reply ≡ Step.cancelled cancelled
  ... | nothing with Store.lookupSaved before token (secondKey token) | Store.lookupSaved before token Step.resultKey
  ... | just saved | just _ = after ≡ before × reply ≡ Step.done saved
  ... | just _ | nothing = after ≡ before × reply ≡ Step.needsRecovery
  ... | nothing | just _ = after ≡ before × reply ≡ Step.needsRecovery
  ... | nothing | nothing = FreshFinalGoal token before after reply

  secondMeaning : ∀ token before → FinalGoal token before
    (proj₁ (second token before)) (proj₂ (second token before))
  secondMeaning token before with Store.lookupSaved before token (firstKey token)
  ... | nothing = refl , refl
  ... | just _ with admit token (Step.registration before)
  ... | just diagnostic = refl , refl
  ... | nothing with Store.lookupCancellation before token
  ... | just cancelled = refl , refl
  ... | nothing with Store.lookupSaved before token (secondKey token) | Store.lookupSaved before token Step.resultKey
  ... | just _ | just _ = refl , refl
  ... | just _ | nothing = refl , refl
  ... | nothing | just _ = refl , refl
  ... | nothing | nothing = freshFinalMeaning token before

  ContinuationGoal : ℕ → Store.World → Prefix.Reply → Store.World → Final.Reply → Set
  ContinuationGoal token middle (Step.done _) after reply = FinalGoal token middle after reply
  ContinuationGoal token middle previous@(Step.needsInput _) after reply = after ≡ middle × reply ≡ previous
  ContinuationGoal token middle Step.needsRecovery after reply = after ≡ middle × reply ≡ Step.needsRecovery
  ContinuationGoal token middle previous@(Step.cancelled _) after reply = after ≡ middle × reply ≡ previous

  -- A completed result owes the intended edge and every resulting posterior.
  -- A dialog owes the exact committed prefix and no final saved answer.
  Goal : ℕ → Store.World → Store.World → Run.Reply → Set
  Goal token before after reply = Σ Store.World (λ middle → Σ Prefix.Reply (λ previous →
    PrefixGoal token before middle previous × ContinuationGoal token middle previous after reply))

  tailMeaning : ∀ token middle previous → ContinuationGoal token middle previous
    (proj₁ (Run.remaining token previous middle)) (proj₂ (Run.remaining token previous middle))
  tailMeaning token middle (Step.done _) = secondMeaning token middle
  tailMeaning token middle (Step.needsInput _) = refl , refl
  tailMeaning token middle Step.needsRecovery = refl , refl
  tailMeaning token middle (Step.cancelled _) = refl , refl

  meaning : ∀ token before → Goal token before
    (proj₁ (Run.evaluate token before)) (proj₂ (Run.evaluate token before))
  meaning token before = proj₁ (prefixExecute token before) , proj₂ (prefixExecute token before) ,
    prefixMeaning token before , tailMeaning token (proj₁ (prefixExecute token before)) (proj₂ (prefixExecute token before))

-- The clock supplier is the external PostgreSQL statement read under the
-- writer lock, inside the transaction that saves the edge and its receipt.
-- Its time is not part of the public request or its reservation metadata.
module Registered (conversion : Conversion.Contract)
  (databaseSum : List Float → Float) (calculator : P.Calculator)
  (serverTime : ℕ → Store.World → ℤ) where
  module C = Core conversion databaseSum calculator
  module G = Ground.Business databaseSum calculator
  module T initial final = AtStatementTime initial final conversion databaseSum calculator

  first : ℤ → ℕ → Store.World → Store.World × Step.Result G.Diagnostic
  first received token = C.Prefix.execute (token , received)
  second : ℤ → ℕ → Store.World → Store.World × Step.Result G.Diagnostic
  second received token = C.second (token , received)
  module Run = Sequence.ObservedTwoPhases ℕ ℤ ℤ G.Diagnostic first second
    (λ received token → C.Prefix.stable (token , received))
    (λ received token → C.secondStable (token , received))
    (λ received token → C.Prefix.expectedPhysical (token , received))
    (λ received token → C.secondPhysical (token , received)) serverTime serverTime

  remainingView : ∀ initial final token previous before →
    Run.remaining final token previous before ≡ T.Run.remaining initial final token previous before
  remainingView initial final token (Step.done _) before = refl
  remainingView initial final token (Step.needsInput _) before = refl
  remainingView initial final token Step.needsRecovery before = refl
  remainingView initial final token (Step.cancelled _) before = refl
  evaluationView : ∀ initial final token before →
    Run.evaluate initial final token before ≡ T.Run.evaluate initial final token before
  evaluationView initial final token before = remainingView initial final token
    (proj₂ (first initial token before)) (proj₁ (first initial token before))

  Goal : ℕ → Store.World → Store.World → Run.Value → Set
  Goal token before after reply = Σ ℤ (λ initial → Σ ℤ (λ final → T.Goal initial final token before after reply))
  meaning : ∀ initial final token before → Goal token before
    (proj₁ (Run.evaluate initial final token before)) (proj₂ (Run.evaluate initial final token before))
  meaning initial final token before = initial , final , subst
    (λ pair → T.Goal initial final token before (proj₁ pair) (proj₂ pair))
    (sym (evaluationView initial final token before)) (T.meaning initial final token before)

  freshPrefix : ∀ received token before changed reply →
    C.Binding.admit token (Step.registration before) ≡ nothing →
    Store.lookupCancellation before token ≡ nothing →
    Store.lookupSaved before token (firstKey token) ≡ nothing →
    Store.lookupSaved before token (secondKey token) ≡ nothing →
    Store.lookupSaved before token Step.resultKey ≡ nothing →
    C.edgeDecision (token , received) before ≡ inj₂ (changed , reply) →
    first received token before ≡ (C.Prefix.Base.firstPublication (token , received) changed reply , Step.done reply)
  freshPrefix received token before changed reply admitted active firstAbsent secondAbsent resultAbsent accepted
    rewrite admitted | active | firstAbsent | secondAbsent | resultAbsent | accepted = refl

  -- Separate the no-write/publication decision from the retry evaluator.
  -- A refused attempt can later receive repaired metadata; only committed
  -- answers must remain fixed.
  FirstPublication : ℤ → ℕ → Store.World → Set
  FirstPublication received token before = Σ Store.World (λ changed → Σ Wire.Value (λ reply →
    C.Binding.admit token (Step.registration before) ≡ nothing ×
    Store.lookupCancellation before token ≡ nothing ×
    Store.lookupSaved before token (firstKey token) ≡ nothing ×
    Store.lookupSaved before token (secondKey token) ≡ nothing ×
    Store.lookupSaved before token Step.resultKey ≡ nothing ×
    C.edgeDecision (token , received) before ≡ inj₂ (changed , reply)))

  firstClassification : ∀ received token before →
    (proj₁ (first received token before) ≡ before) ⊎ FirstPublication received token before
  firstClassification received token before with C.Binding.admit token (Step.registration before) in admission
  ... | just _ = inj₁ refl
  ... | nothing with Store.lookupCancellation before token in cancellation
  ... | just _ = inj₁ refl
  ... | nothing with Store.lookupSaved before token (firstKey token) in firstSaved
    | Store.lookupSaved before token (secondKey token) in secondSaved
    | Store.lookupSaved before token Step.resultKey in resultSaved
  ... | just _ | nothing | nothing = inj₁ refl
  ... | just _ | just _ | just _ = inj₁ refl
  ... | just _ | nothing | just _ = inj₁ refl
  ... | just _ | just _ | nothing = inj₁ refl
  ... | nothing | nothing | just _ = inj₁ refl
  ... | nothing | just _ | nothing = inj₁ refl
  ... | nothing | just _ | just _ = inj₁ refl
  ... | nothing | nothing | nothing with C.edgeDecision (token , received) before in accepted
  ... | inj₁ _ = inj₁ refl
  ... | inj₂ (changed , reply) = inj₂ (changed , reply , refl , refl , refl , refl , refl , refl)

  firstFamilyPreserved : ∀ wantedFirst wantedFinal received token before →
    Σ ℤ (λ originalFirst → Σ ℤ (λ originalFinal →
      Run.evaluate wantedFirst wantedFinal token (proj₁ (first received token before)) ≡
      Run.evaluate originalFirst originalFinal token before))
  firstFamilyPreserved wantedFirst wantedFinal received token before with firstClassification received token before
  ... | inj₁ unchanged = wantedFirst , wantedFinal , cong (Run.evaluate wantedFirst wantedFinal token) unchanged
  ... | inj₂ (changed , reply , admission , cancellation , firstSaved , secondSaved , resultSaved , accepted) =
    received , wantedFinal , trans
      (cong (Run.evaluate wantedFirst wantedFinal token) (cong proj₁ original))
      (trans afterReplay (sym beforeReplay))
    where
    input = token , received
    middle = C.Prefix.Base.firstPublication input changed reply
    original = freshPrefix received token before changed reply admission cancellation firstSaved secondSaved resultSaved accepted
    admitted = trans (cong (C.Binding.admit token)
      (C.Prefix.keepsRegistration input before changed reply accepted)) admission
    active = trans (C.Prefix.keepsCancellation input before changed reply accepted) cancellation
    firstPublished = C.Prefix.Base.firstReadable input before changed reply accepted firstSaved
    nextAbsent = trans (C.Prefix.keepsNext input before changed reply accepted) secondSaved
    finalAbsent = C.Prefix.Base.firstHasNoResult input before changed reply accepted resultSaved
    replay = T.prefixPendingReplay wantedFirst wantedFinal token middle reply admitted active firstPublished nextAbsent finalAbsent
    afterReplay = cong (λ pair → Run.remaining wantedFinal token (proj₂ pair) (proj₁ pair)) replay
    beforeReplay = cong (λ pair → Run.remaining wantedFinal token (proj₂ pair) (proj₁ pair)) original

  fullReplay : ∀ initial final token before saved next result →
    C.Binding.admit token (Step.registration before) ≡ nothing →
    Store.lookupCancellation before token ≡ nothing →
    Store.lookupSaved before token (firstKey token) ≡ just saved →
    Store.lookupSaved before token (secondKey token) ≡ just next →
    Store.lookupSaved before token Step.resultKey ≡ just result →
    Run.evaluate initial final token before ≡ (before , Step.done next)
  fullReplay initial final token before saved next result admitted active firstSaved nextSaved resultSaved = trans
    (evaluationView initial final token before)
    (trans
      (cong (λ pair → T.Run.remaining initial final token (proj₂ pair) (proj₁ pair))
        (T.prefixCompleteReplay initial final token before saved next result admitted active firstSaved nextSaved resultSaved))
      (T.secondCompleteReplay initial final token before saved next result admitted active firstSaved nextSaved resultSaved))

  SecondPublication : ℤ → ℕ → Store.World → Set
  SecondPublication received token before = Σ Store.World (λ changed → Σ Wire.Value (λ reply → Σ Wire.Value (λ saved →
    C.Binding.admit token (Step.registration before) ≡ nothing ×
    Store.lookupCancellation before token ≡ nothing ×
    Store.lookupSaved before token (firstKey token) ≡ just saved ×
    Store.lookupSaved before token (secondKey token) ≡ nothing ×
    Store.lookupSaved before token Step.resultKey ≡ nothing ×
    C.finalDecision (token , received) before ≡ inj₂ (changed , reply))))

  secondClassification : ∀ received token before →
    (proj₁ (second received token before) ≡ before) ⊎ SecondPublication received token before
  secondClassification received token before with Store.lookupSaved before token (firstKey token) in firstSaved
  ... | nothing = inj₁ refl
  ... | just saved with C.Binding.admit token (Step.registration before) in admission
  ... | just _ = inj₁ refl
  ... | nothing with Store.lookupCancellation before token in active
  ... | just _ = inj₁ refl
  ... | nothing with Store.lookupSaved before token (secondKey token) in nextSaved
    | Store.lookupSaved before token Step.resultKey in resultSaved
  ... | just _ | just _ = inj₁ refl
  ... | just _ | nothing = inj₁ refl
  ... | nothing | just _ = inj₁ refl
  ... | nothing | nothing with C.finalDecision (token , received) before in accepted
  ... | inj₁ _ = inj₁ refl
  ... | inj₂ (changed , reply) = inj₂ (changed , reply , saved , refl , refl , refl , refl , refl , refl)

  secondKeepsFamily : ∀ initial wanted received token before → Σ ℤ (λ original →
    Run.evaluate initial wanted token (proj₁ (second received token before)) ≡ Run.evaluate initial original token before)
  secondKeepsFamily initial wanted received token before with secondClassification received token before
  ... | inj₁ unchanged = wanted , cong (Run.evaluate initial wanted token) unchanged
  ... | inj₂ (changed , reply , saved , admission , active , firstSaved , nextSaved , resultSaved , accepted) = received , trans
    (cong (Run.evaluate initial wanted token) (cong proj₁ originalFinal))
    (trans afterReplay (sym beforePublished))
    where
    input = token , received
    published = C.Final.Kernel.publication input changed reply
    originalFinal = T.secondFresh initial received token before saved changed reply admission active firstSaved nextSaved resultSaved accepted
    admittedPub = trans (cong (C.Binding.admit token)
      (C.Final.Kernel.publicationKeepsRegistration input before changed reply accepted)) admission
    activePub = trans (C.Final.Kernel.publicationKeepsCancellation input before changed reply accepted) active
    firstPub = trans (T.publishedFirst initial received token before changed reply accepted) firstSaved
    nextPub = C.Final.Kernel.publishedStepReadable input before changed reply accepted nextSaved
    resultPub = C.Final.Kernel.publishedResultReadable input before changed reply accepted resultSaved
    afterReplay = fullReplay initial wanted token published saved reply reply admittedPub activePub firstPub nextPub resultPub
    beforePublished = trans (evaluationView initial received token before)
      (T.originalEvaluation initial received token before changed reply saved admission active firstSaved nextSaved resultSaved accepted)

  module Certified = Run.Certified firstFamilyPreserved secondKeepsFamily Goal meaning
  operation = Certified.operation

  record CacheReceipts (token : ℕ) (before : Store.World) : Set where
    field cachedFirstValue cachedFinalValue : Wire.Value
          cachedAdmitted : C.Binding.admit token (Step.registration before) ≡ nothing
          cachedActive : Store.lookupCancellation before token ≡ nothing
          cachedFirst : Store.lookupSaved before token (firstKey token) ≡ just cachedFirstValue
          cachedSecond : Store.lookupSaved before token (secondKey token) ≡ just cachedFinalValue
          cachedResult : Store.lookupSaved before token Step.resultKey ≡ just cachedFinalValue

  CacheInvariant : ℕ → Store.World → Set
  CacheInvariant token before = (Store.lookupSaved before token Step.resultKey ≡ nothing) ⊎ CacheReceipts token before

  firstKeepsCache : ∀ received token before → CacheInvariant token before →
    CacheInvariant token (proj₁ (first received token before))
  firstKeepsCache received token before old with firstClassification received token before
  ... | inj₁ unchanged = subst (CacheInvariant token) (sym unchanged) old
  ... | inj₂ (changed , reply , admitted , active , firstAbsent , nextAbsent , resultAbsent , accepted) = inj₁ (trans
    (cong (λ outcome → Store.lookupSaved (proj₁ outcome) token Step.resultKey)
      (freshPrefix received token before changed reply admitted active firstAbsent nextAbsent resultAbsent accepted))
    (C.Prefix.Base.firstHasNoResult (token , received) before changed reply accepted resultAbsent))

  secondKeepsCache : ∀ received token before → CacheInvariant token before →
    CacheInvariant token (proj₁ (second received token before))
  secondKeepsCache received token before old with secondClassification received token before
  ... | inj₁ unchanged = subst (CacheInvariant token) (sym unchanged) old
  ... | inj₂ (changed , reply , saved , admitted , active , firstSaved , nextAbsent , resultAbsent , accepted) =
    inj₂ (subst (CacheReceipts token) (sym (cong proj₁ actualFinal)) packet)
    where
    input = token , received
    published = C.Final.Kernel.publication input changed reply
    actualFinal = T.secondFresh received received token before saved changed reply admitted active firstSaved nextAbsent resultAbsent accepted
    packet : CacheReceipts token published
    packet = record
      { cachedFirstValue = saved; cachedFinalValue = reply
      ; cachedAdmitted = trans (cong (C.Binding.admit token)
          (C.Final.Kernel.publicationKeepsRegistration input before changed reply accepted)) admitted
      ; cachedActive = trans (C.Final.Kernel.publicationKeepsCancellation input before changed reply accepted) active
      ; cachedFirst = trans (T.publishedFirst received received token before changed reply accepted) firstSaved
      ; cachedSecond = C.Final.Kernel.publishedStepReadable input before changed reply accepted nextAbsent
      ; cachedResult = C.Final.Kernel.publishedResultReadable input before changed reply accepted resultAbsent }

  atomicKeepsCache : ∀ token before after effect reply → Run.Owned token effect →
    Run.Atomic before effect reply after → CacheInvariant token before → CacheInvariant token after
  atomicKeepsCache token before after .(Run.prefix token) (received , reply) Run.firstOwned physical old =
    subst (CacheInvariant token)
      (sym (cong proj₁ (Run.First.atomicObservation received token before after reply physical)))
      (firstKeepsCache received token before old)
  atomicKeepsCache token before after .(Run.finish token) (received , reply) Run.secondOwned physical old =
    subst (CacheInvariant token)
      (sym (cong proj₁ (Run.Second.atomicObservation received token before after reply physical)))
      (secondKeepsCache received token before old)

  changesKeepCache : ∀ token before events after → All (λ event → Run.Owned token (proj₁ event)) events →
    Run.X.Changes before events after → CacheInvariant token before → CacheInvariant token after
  changesKeepCache token before [] .before [] (Run.X.unchanged _) old = old
  changesKeepCache token before ((effect , reply) ∷ events) after (owner ∷ owners)
    (Run.X.changed _ _ _ middle physical later) old = changesKeepCache token middle events after owners later
      (atomicKeepsCache token before middle effect reply owner physical old)

  interruptedCache : ∀ token initial current → Store.lookupSaved initial token Step.resultKey ≡ nothing →
    Run.X.Interrupted (Run.script token) initial current → CacheInvariant token current
  interruptedCache token initial current absent (Run.X.atPrefix events residual .current observed physical) =
    changesKeepCache token initial events current
      (proj₁ (Run.prefixScoped token (Run.script token) events residual (Run.scriptScoped token) observed)) physical (inj₁ absent)
  interruptedCache token initial current absent
    (Run.X.beforeReply events effect continuation middle reply .current observed physical active)
    with Run.prefixScoped token (Run.script token) events (Run.E.ask effect continuation) (Run.scriptScoped token) observed
  ... | owners , scoped = atomicKeepsCache token middle current effect reply
    (Run.activeOwned token effect continuation scoped) active
    (changesKeepCache token initial events middle owners physical (inj₁ absent))

  cachedEvaluation : ∀ initial final token before raw → CacheReceipts token before →
    Store.lookupSaved before token Step.resultKey ≡ just raw →
    Run.evaluate initial final token before ≡ (before , Step.done raw)
  cachedEvaluation initial final token before raw packet present = trans
    (fullReplay initial final token before (CacheReceipts.cachedFirstValue packet)
      (CacheReceipts.cachedFinalValue packet) (CacheReceipts.cachedFinalValue packet)
      (CacheReceipts.cachedAdmitted packet) (CacheReceipts.cachedActive packet)
      (CacheReceipts.cachedFirst packet) (CacheReceipts.cachedSecond packet) (CacheReceipts.cachedResult packet))
    (cong (λ value → before , Step.done value) (sameValue (trans (sym (CacheReceipts.cachedResult packet)) present)))
    where
    sameValue : ∀ {first second : Wire.Value} → just first ≡ just second → first ≡ second
    sameValue refl = refl

  cachedReplay : ∀ token initial current raw → Store.lookupSaved initial token Step.resultKey ≡ nothing →
    Run.X.Interrupted (Run.script token) initial current → Store.lookupSaved current token Step.resultKey ≡ just raw →
    Run.X.Completed (Run.script token) current current (Step.done raw)
  cachedReplay token initial current raw absent crash present with interruptedCache token initial current absent crash
  ... | inj₁ missing with trans (sym missing) present
  ... | ()
  cachedReplay token initial current raw absent crash present | inj₂ packet with Certified.progress token current
  ... | after , reply , completion with Run.completedObservation token current after reply completion
  ... | first , final , observed = subst
    (λ outcome → Run.X.Completed (Run.script token) current (proj₁ outcome) (proj₂ outcome))
    (trans observed (cachedEvaluation first final token current raw packet present)) completion
