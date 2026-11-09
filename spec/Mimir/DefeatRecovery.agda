{-# OPTIONS --safe #-}
-- A durable defeat edge survives a later request for a numerical decision.
-- Retries reuse the original answers at both independently committed phases.
module Mimir.DefeatRecovery where

open import Data.Empty using (⊥)
open import Data.Float.Base using (Float)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_)
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

module Business (databaseSum : List Float → Float) (calculator : P.Calculator) where
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

  edge : Request → Store.World → Outcome
  edge (request from to weight) before with Writes.insertEdge from to Review.defeats weight before
  ... | Writes.invalidWeight = inj₁ (requestFault weightFault)
  ... | Writes.missingEndpoint = inj₁ (requestFault (endpointFault from before))
  ... | Writes.applied after = inj₂ (after , answer)

  -- One requested independent contribution, retaining every other component.
  EdgeGoal : Request → Store.World → Outcome → Set
  EdgeGoal (request from to weight) before outcome with Writes.insertEdge from to Review.defeats weight before
  ... | Writes.invalidWeight = outcome ≡ inj₁ (requestFault weightFault)
  ... | Writes.missingEndpoint = outcome ≡ inj₁ (requestFault (endpointFault from before))
  ... | Writes.applied after = outcome ≡ inj₂ (after , answer)

  edgeMeaning : ∀ requested before → EdgeGoal requested before (edge requested before)
  edgeMeaning (request from to weight) before with Writes.insertEdge from to Review.defeats weight before
  ... | Writes.invalidWeight = refl
  ... | Writes.missingEndpoint = refl
  ... | Writes.applied after = refl

  edgeKeepsJournal : ∀ requested before after reply → edge requested before ≡ inj₂ (after , reply) →
    Store.World.operations after ≡ Store.World.operations before
  edgeKeepsJournal (request from to weight) before after reply accepted
    with Writes.insertEdge from to Review.defeats weight before in inserted
  ... | Writes.invalidWeight with accepted
  ... | ()
  edgeKeepsJournal (request from to weight) before after reply accepted | Writes.missingEndpoint with accepted
  ... | ()
  edgeKeepsJournal (request from to weight) before after reply accepted | Writes.applied changed with accepted
  ... | refl = Writes.insertEdgeKeepsJournal from to Review.defeats weight before changed inserted

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

module Registered (conversion : Conversion.Contract)
  (databaseSum : List Float → Float) (calculator : P.Calculator) where
  module B = Business databaseSum calculator
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
  decode raw with D.readTool Tools.recordDefeat raw
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ (Public.mutation (Mutation.edge from to Review.defeats weight)) = inj₂ (request from to weight)
  ... | inj₂ _ = inj₁ mismatch

  original : ℕ → Step.Registration → Validation.Fault ⊎ (Request × ℤ)
  original token registration with Admission.resolvePair descriptor token registration
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ (reserved , binding) with Store.BindingRow.settings binding
  ... | Wire.object [] = Decode.mapResult (λ requested → requested , Store.ReservationRow.reservedAt reserved)
    (decode (Store.BindingRow.arguments binding))
  ... | _ = inj₁ mismatch

  admit : ℕ → Step.Registration → Maybe G.Diagnostic
  admit token registration with original token registration
  ... | inj₁ fault = just (G.requestFault fault)
  ... | inj₂ _ = nothing

  edgeDecision : ℕ → Store.World → B.Outcome
  edgeDecision token before with original token (Step.registration before)
  ... | inj₁ fault = inj₁ (G.requestFault fault)
  ... | inj₂ (requested , publicationTime) = B.edge requested before

  edgeJournal : ∀ token before after reply → edgeDecision token before ≡ inj₂ (after , reply) →
    Store.World.operations after ≡ Store.World.operations before
  edgeJournal token before after reply accepted with original token (Step.registration before)
  ... | inj₁ fault with accepted
  ... | ()
  edgeJournal token before after reply accepted | inj₂ (requested , publicationTime) =
    B.edgeKeepsJournal requested before after reply accepted

  module Prefix = Sequence.SavedPrefix ℕ G.Diagnostic (λ token → token)
    firstKey secondKey firstDistinct keysDifferent edgeDecision edgeJournal admit

  finalDecision : ℕ → Store.World → B.Outcome
  finalDecision token before with original token (Step.registration before)
  ... | inj₁ fault = inj₁ (G.requestFault fault)
  ... | inj₂ (requested , publicationTime) = proj₁ (B.checked publicationTime requested before)

  finalJournal : ∀ token before after reply → finalDecision token before ≡ inj₂ (after , reply) →
    Store.World.operations after ≡ Store.World.operations before
  finalJournal token before after reply accepted with original token (Step.registration before)
  ... | inj₁ fault with accepted
  ... | ()
  finalJournal token before after reply accepted | inj₂ (requested , publicationTime) =
    B.finalKeepsJournal publicationTime requested before after reply accepted

  module Final = Step.Admitted ℕ G.Diagnostic (λ token → token) secondKey secondDistinct
    finalDecision finalJournal admit

  finalPreservesFirst : ∀ token before →
    Store.lookupSaved (proj₁ (Final.execute token before)) token (firstKey token) ≡
      Store.lookupSaved before token (firstKey token)
  finalPreservesFirst token before with admit token (Step.registration before)
  ... | just _ = refl
  ... | nothing with Store.lookupCancellation before token
  ... | just _ = refl
  ... | nothing with Store.lookupSaved before token (secondKey token) | Store.lookupSaved before token Step.resultKey
  ... | just _ | just _ = refl
  ... | just _ | nothing = refl
  ... | nothing | just _ = refl
  ... | nothing | nothing with finalDecision token before in accepted
  ... | inj₁ _ = refl
  ... | inj₂ (changed , reply) = trans
    (Store.otherSavedAnswerPreserved (Final.Kernel.firstPublication token changed reply) token Step.resultKey reply
      token (firstKey token) (λ same → firstDistinct token (proj₂ same)))
    (trans (Store.otherSavedAnswerPreserved changed token (secondKey token) reply token (firstKey token)
      (λ same → keysDifferent token (proj₂ same)))
      (Final.Kernel.changedLookup token before changed reply (firstKey token) accepted))

  second : ℕ → Store.World → Store.World × Final.Reply
  second token before with Store.lookupSaved before token (firstKey token)
  ... | nothing = before , Step.needsRecovery
  ... | just _ = Final.execute token before

  secondStable : ∀ token before → second token (proj₁ (second token before)) ≡ second token before
  secondStable token before with Store.lookupSaved before token (firstKey token) in saved
  ... | nothing rewrite saved = refl
  ... | just _ rewrite finalPreservesFirst token before | saved = Final.stable token before

  secondPhysical : ∀ token before → DB.Atomic before (proj₁ (second token before))
    (Step.receiptFor (proj₂ (second token before))) (proj₁ (second token before))
  secondPhysical token before with Store.lookupSaved before token (firstKey token)
  ... | nothing = DB.abortedNone
  ... | just _ = Final.expectedPhysical token before

  module Run = Sequence.TwoPhases ℕ G.Diagnostic Prefix.execute second
    Prefix.stable secondStable Prefix.expectedPhysical secondPhysical

  firstKeepsOutcome : ∀ token before → Run.evaluate token (proj₁ (Prefix.execute token before)) ≡ Run.evaluate token before
  firstKeepsOutcome token before = cong (λ result → Run.remaining token (proj₂ result) (proj₁ result))
    (Prefix.stable token before)

  publishedFirst : ∀ token before changed reply → finalDecision token before ≡ inj₂ (changed , reply) →
    Store.lookupSaved (Final.Kernel.publication token changed reply) token (firstKey token) ≡
      Store.lookupSaved before token (firstKey token)
  publishedFirst token before changed reply accepted = trans
    (Store.otherSavedAnswerPreserved (Final.Kernel.firstPublication token changed reply) token Step.resultKey reply
      token (firstKey token) (λ same → firstDistinct token (proj₂ same)))
    (trans (Store.otherSavedAnswerPreserved changed token (secondKey token) reply token (firstKey token)
      (λ same → keysDifferent token (proj₂ same)))
      (Final.Kernel.changedLookup token before changed reply (firstKey token) accepted))

  prefixCompleteReplay : ∀ token before saved next result →
    admit token (Step.registration before) ≡ nothing →
    Store.lookupCancellation before token ≡ nothing →
    Store.lookupSaved before token (firstKey token) ≡ just saved →
    Store.lookupSaved before token (secondKey token) ≡ just next →
    Store.lookupSaved before token Step.resultKey ≡ just result →
    Prefix.execute token before ≡ (before , Step.done saved)
  prefixCompleteReplay token before saved next result admitted active firstSaved nextSaved resultSaved
    rewrite admitted | active | firstSaved | nextSaved | resultSaved = refl

  prefixPendingReplay : ∀ token before saved →
    admit token (Step.registration before) ≡ nothing →
    Store.lookupCancellation before token ≡ nothing →
    Store.lookupSaved before token (firstKey token) ≡ just saved →
    Store.lookupSaved before token (secondKey token) ≡ nothing →
    Store.lookupSaved before token Step.resultKey ≡ nothing →
    Prefix.execute token before ≡ (before , Step.done saved)
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
    second token before ≡ (Final.Kernel.publication token changed reply , Step.done reply)
  secondFresh token before saved changed reply admitted active firstSaved nextSaved resultSaved accepted
    rewrite firstSaved | admitted | active | nextSaved | resultSaved | accepted = refl

  publishedEvaluation : ∀ token before changed reply saved →
    admit token (Step.registration before) ≡ nothing →
    Store.lookupCancellation before token ≡ nothing →
    Store.lookupSaved before token (firstKey token) ≡ just saved →
    Store.lookupSaved before token (secondKey token) ≡ nothing →
    Store.lookupSaved before token Step.resultKey ≡ nothing →
    finalDecision token before ≡ inj₂ (changed , reply) →
    Run.evaluate token (Final.Kernel.publication token changed reply) ≡
      (Final.Kernel.publication token changed reply , Step.done reply)
  publishedEvaluation token before changed reply saved admitted active firstSaved secondAbsent resultAbsent accepted = trans
    (cong (λ result → Run.remaining token (proj₂ result) (proj₁ result))
      (prefixCompleteReplay token published saved reply reply publicationAdmitted publicationActive
        publicationFirst publicationSecond publicationResult))
    (secondCompleteReplay token published saved reply reply publicationAdmitted publicationActive
      publicationFirst publicationSecond publicationResult)
    where
    published = Final.Kernel.publication token changed reply
    publicationAdmitted = trans (cong (admit token)
      (Final.Kernel.publicationKeepsRegistration token before changed reply accepted)) admitted
    publicationActive = trans (Final.Kernel.publicationKeepsCancellation token before changed reply accepted) active
    publicationFirst = trans (publishedFirst token before changed reply accepted) firstSaved
    publicationSecond = Final.Kernel.publishedStepReadable token before changed reply accepted secondAbsent
    publicationResult = Final.Kernel.publishedResultReadable token before changed reply accepted resultAbsent

  originalEvaluation : ∀ token before changed reply saved →
    admit token (Step.registration before) ≡ nothing →
    Store.lookupCancellation before token ≡ nothing →
    Store.lookupSaved before token (firstKey token) ≡ just saved →
    Store.lookupSaved before token (secondKey token) ≡ nothing →
    Store.lookupSaved before token Step.resultKey ≡ nothing →
    finalDecision token before ≡ inj₂ (changed , reply) →
    Run.evaluate token before ≡ (Final.Kernel.publication token changed reply , Step.done reply)
  originalEvaluation token before changed reply saved admitted active firstSaved secondAbsent resultAbsent accepted = trans
    (cong (λ result → Run.remaining token (proj₂ result) (proj₁ result))
      (prefixPendingReplay token before saved admitted active firstSaved secondAbsent resultAbsent))
    (secondFresh token before saved changed reply admitted active firstSaved secondAbsent resultAbsent accepted)

  -- Keep the complete outcome opaque while analysing a receipt. This prevents
  -- case splitting from rewriting the two sides inside their shared parser.
  abstract
    observation : ℕ → Store.World → Store.World × Run.Reply
    observation = Run.evaluate

    observationDefinition : ∀ token before → observation token before ≡ Run.evaluate token before
    observationDefinition token before = refl

  secondKeepsObservation : ∀ token before → observation token (proj₁ (second token before)) ≡ observation token before
  secondKeepsObservation token before with Store.lookupSaved before token (firstKey token) in firstSaved
  ... | nothing = refl
  ... | just saved with admit token (Step.registration before) in admitted
  ... | just diagnostic = refl
  ... | nothing with Store.lookupCancellation before token in active
  ... | just cancelled = refl
  ... | nothing with Store.lookupSaved before token (secondKey token) in secondSaved
    | Store.lookupSaved before token Step.resultKey in resultSaved
  ... | just _ | just _ = refl
  ... | just _ | nothing = refl
  ... | nothing | just _ = refl
  ... | nothing | nothing with finalDecision token before in accepted
  ... | inj₁ diagnostic = refl
  ... | inj₂ (changed , reply) = trans (observationDefinition token (Final.Kernel.publication token changed reply))
    (trans (publishedEvaluation token before changed reply saved admitted active firstSaved secondSaved resultSaved accepted)
      (trans (sym (originalEvaluation token before changed reply saved admitted active firstSaved secondSaved resultSaved accepted))
        (sym (observationDefinition token before))))

  secondKeepsOutcome : ∀ token before → Run.evaluate token (proj₁ (second token before)) ≡ Run.evaluate token before
  secondKeepsOutcome token before = trans
    (sym (observationDefinition token (proj₁ (second token before))))
    (trans (secondKeepsObservation token before) (observationDefinition token before))

  EdgeIntent : ℕ → Store.World → B.Outcome → Set
  EdgeIntent token before outcome with original token (Step.registration before)
  ... | inj₁ fault = outcome ≡ inj₁ (G.requestFault fault)
  ... | inj₂ (requested , publicationTime) = B.EdgeGoal requested before outcome

  edgeDecisionMeaning : ∀ token before → EdgeIntent token before (edgeDecision token before)
  edgeDecisionMeaning token before with original token (Step.registration before)
  ... | inj₁ fault = refl
  ... | inj₂ (requested , publicationTime) = B.edgeMeaning requested before

  FreshPrefixGoal : ℕ → Store.World → Store.World → Prefix.Reply → Set
  FreshPrefixGoal token before after (Step.done reply) = Σ Store.World (λ changed →
    EdgeIntent token before (inj₂ (changed , reply)) ×
      after ≡ Prefix.Base.firstPublication token changed reply)
  FreshPrefixGoal token before after (Step.needsInput diagnostic) =
    after ≡ before × EdgeIntent token before (inj₁ diagnostic)
  FreshPrefixGoal token before after _ = ⊥

  freshPrefixMeaning : ∀ token before → FreshPrefixGoal token before
    (proj₁ (Prefix.fresh token before)) (proj₂ (Prefix.fresh token before))
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
    (proj₁ (Prefix.execute token before)) (proj₂ (Prefix.execute token before))
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
  ... | inj₂ (requested , publicationTime) = B.FinalGoal publicationTime requested before outcome

  finalDecisionMeaning : ∀ token before → FinalIntent token before (finalDecision token before)
  finalDecisionMeaning token before with original token (Step.registration before)
  ... | inj₁ fault = refl
  ... | inj₂ (requested , publicationTime) = proj₂ (B.checked publicationTime requested before)

  FreshFinalGoal : ℕ → Store.World → Store.World → Final.Reply → Set
  FreshFinalGoal token before after (Step.done reply) = Σ Store.World (λ changed →
    FinalIntent token before (inj₂ (changed , reply)) ×
      after ≡ Final.Kernel.publication token changed reply)
  FreshFinalGoal token before after (Step.needsInput diagnostic) =
    after ≡ before × FinalIntent token before (inj₁ diagnostic)
  FreshFinalGoal token before after _ = ⊥

  freshFinalMeaning : ∀ token before → FreshFinalGoal token before
    (proj₁ (Final.Kernel.fresh token before)) (proj₂ (Final.Kernel.fresh token before))
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
  meaning token before = proj₁ (Prefix.execute token before) , proj₂ (Prefix.execute token before) ,
    prefixMeaning token before , tailMeaning token (proj₁ (Prefix.execute token before)) (proj₂ (Prefix.execute token before))

  module Certified = Run.Certified firstKeepsOutcome secondKeepsOutcome Goal meaning
  operation = Certified.operation
