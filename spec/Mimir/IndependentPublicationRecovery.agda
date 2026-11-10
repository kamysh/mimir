{-# OPTIONS --safe #-}
-- PostgreSQL allocates the owner; source reads and the exact embedding call
-- prepare its packet; one final transaction publishes the belief and sources.
module Mimir.IndependentPublicationRecovery where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Float.Base using (Float)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.BeliefEmbedding as Embedding
import Mimir.CandidateGraph as Graph
import Mimir.DatabaseTransaction as DB
import Mimir.IndependentBeliefRecovery as Belief
import Mimir.PosteriorComputation as Posterior
import Mimir.PublicEncoding as Encoding
import Mimir.RecoverableStoreSequence as Sequence
import Mimir.RecoverableStoreStep as Step
import Mimir.StandardLibrary as Conversion
import Mimir.StructuredValue as Wire
import Mimir.Validation as Validation
import Mimir.ConfigurationValues as Config
import Mimir.ProjectDeletion as Project
import Mimir.Effects as Effects
import Mimir.Recovery as Recovery
import Data.List.Properties as Lists
open import Data.List using (_++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)

-- This snapshot and provider response are internal observations. The public
-- protocol below constructs them from its source-read and embedding effects.
data Packet : Set where
  sourceUnavailable : Text → Packet
  packet : Store.World → Text ⊎ List Store.Vector → Packet

owner : ℕ → List Store.EmbeddingOwnerRow → Maybe Store.EmbeddingOwnerRow
owner token [] = nothing
owner token (row ∷ rest) with Store.EmbeddingOwnerRow.operationToken row
... | nothing = owner token rest
... | just linked with token ≟ linked
... | yes _ = just row
... | no _ = owner token rest

allocation : Store.EmbeddingOwnerRow → Belief.Allocation
allocation row = Belief.allocated (Store.EmbeddingOwnerRow.token row) (Store.EmbeddingOwnerRow.reservedAt row)

publicationDistinct : ∀ token → Belief.publicationKey token ≡ Step.resultKey → ⊥
publicationDistinct token ()

module Registered (format : Encoding.Formatting) (conversion : Conversion.Contract)
  (databaseSum : List Float → Float) (calculator : Posterior.Calculator)
  (allocate : ℕ → Store.World → Belief.Allocation) where
  module B = Belief.Business format databaseSum calculator
  module O metadata = Belief.OwnerPhase format conversion databaseSum calculator metadata
  -- Admission does not depend on a subsequently observed allocation.
  module Original = Belief.Binding format conversion databaseSum calculator
  original = Original.original
  admit = Original.admit

  first : Belief.Allocation → ℕ → Store.World → Store.World × Step.Result B.Diagnostic
  first metadata = O.Saved.execute metadata
  firstStable = λ metadata → O.Saved.stable metadata
  firstPhysical = λ metadata → O.Saved.expectedPhysical metadata

  freshPrefix : ∀ metadata token before changed reply → admit token (Step.registration before) ≡ nothing →
    Store.lookupCancellation before token ≡ nothing → Store.lookupSaved before token (Belief.ownerKey token) ≡ nothing →
    Store.lookupSaved before token (Belief.publicationKey token) ≡ nothing → Store.lookupSaved before token Step.resultKey ≡ nothing →
    O.decide metadata token before ≡ inj₂ (changed , reply) →
    first metadata token before ≡ (O.Saved.Base.firstPublication metadata token changed reply , Step.done reply)
  freshPrefix metadata token before changed reply admitted active firstSaved nextSaved resultSaved accepted
    rewrite admitted | active | firstSaved | nextSaved | resultSaved | accepted = refl

  FirstPublication : Belief.Allocation → ℕ → Store.World → Set
  FirstPublication metadata token before = Σ Store.World (λ changed → Σ Wire.Value (λ reply →
    admit token (Step.registration before) ≡ nothing × Store.lookupCancellation before token ≡ nothing ×
    Store.lookupSaved before token (Belief.ownerKey token) ≡ nothing ×
    Store.lookupSaved before token (Belief.publicationKey token) ≡ nothing ×
    Store.lookupSaved before token Step.resultKey ≡ nothing × O.decide metadata token before ≡ inj₂ (changed , reply)))

  firstClassification : ∀ metadata token before → (proj₁ (first metadata token before) ≡ before) ⊎ FirstPublication metadata token before
  firstClassification metadata token before with admit token (Step.registration before)
  ... | just _ = inj₁ refl
  ... | nothing with Store.lookupCancellation before token
  ... | just _ = inj₁ refl
  ... | nothing with Store.lookupSaved before token (Belief.ownerKey token)
    | Store.lookupSaved before token (Belief.publicationKey token) | Store.lookupSaved before token Step.resultKey
  ... | just _ | nothing | nothing = inj₁ refl
  ... | just _ | just _ | just _ = inj₁ refl
  ... | just _ | nothing | just _ = inj₁ refl
  ... | just _ | just _ | nothing = inj₁ refl
  ... | nothing | nothing | just _ = inj₁ refl
  ... | nothing | just _ | nothing = inj₁ refl
  ... | nothing | just _ | just _ = inj₁ refl
  ... | nothing | nothing | nothing with O.decide metadata token before
  ... | inj₁ _ = inj₁ refl
  ... | inj₂ (changed , reply) = inj₂ (changed , reply , refl , refl , refl , refl , refl , refl)

  missingOwner : B.Diagnostic
  missingOwner = B.preparation (Embedding.preparationDecision Embedding.Correction.arguments
    (Validation.key "operation_token" ∷ [])
    (toList "The original preparation owner is absent. Read this token's outcome and cancellation before deciding whether to reserve corrected work. No belief was stored."))

  preparationFailure : Text → B.Diagnostic
  preparationFailure reason = B.preparation (Embedding.preparationDecision Embedding.Correction.configuration
    (Validation.key "embeddings" ∷ []) reason)

  sourceFailure : Text → B.Diagnostic
  sourceFailure reason = B.preparation (Embedding.preparationDecision Embedding.Correction.arguments
    (Validation.key "grounding" ∷ []) reason)

  Selection = B.Diagnostic ⊎ (Graph.BeliefValues × Embedding.Prepared)

  -- The source packet is derived from the observed database, not supplied as
  -- an expected belief or supporting rows by the caller.
  selectVectors : Graph.BeliefValues → List Embedding.Support → Text ⊎ List Store.Vector → Selection
  selectVectors belief support (inj₁ reason) = inj₁ (preparationFailure reason)
  selectVectors belief [] (inj₂ vectors) = inj₁ (sourceFailure
    (toList "Supply an indexed-document supporting passage and explanation before publication."))
  selectVectors belief (first ∷ rest) (inj₂ (vector ∷ [])) with Embedding.usableVector vector
  ... | false = inj₁ (preparationFailure (toList "The backend returned an empty, nonfinite or zero vector; no belief was stored."))
  ... | true = inj₂ (belief , Embedding.prepared vector first rest)
  selectVectors belief (_ ∷ _) (inj₂ _) = inj₁ (preparationFailure
    (toList "The backend must return exactly one complete vector for the original belief; no belief was stored."))

  selectSupport : Belief.Request → Graph.BeliefValues → Packet → Selection
  selectSupport requested belief (sourceUnavailable reason) = inj₁ (sourceFailure reason)
  selectSupport requested belief (packet snapshot response) with Embedding.selectSupport belief snapshot (Belief.Request.grounding requested)
  ... | inj₁ reason = inj₁ (sourceFailure reason)
  ... | inj₂ support = selectVectors belief support response

  select : ℕ → Belief.Request → Packet → Selection
  select token requested (sourceUnavailable reason) = inj₁ (B.preparation
    (Embedding.preparationDecision Embedding.Correction.configuration (Validation.key "database" ∷ []) reason))
  select token requested observed@(packet snapshot response) with owner token (Store.World.embeddingOwners snapshot)
  ... | nothing = inj₁ missingOwner
  ... | just row with Belief.initial requested (allocation row)
  ... | nothing = inj₁ (B.requestFault Original.mismatch)
  ... | just belief = selectSupport requested belief observed

  selectedOutcome : Belief.Request → Selection → Store.World → B.Outcome
  selectedOutcome requested (inj₁ diagnostic) before = inj₁ diagnostic
  selectedOutcome requested (inj₂ (belief , value)) before = proj₁ (B.checked
    (Graph.BeliefValues.created belief) belief (just (Belief.Request.provenance requested)) value before)

  decide : Packet → ℕ → Store.World → B.Outcome
  decide observed token before with original token (Step.registration before)
  ... | inj₁ fault = inj₁ (B.requestFault fault)
  ... | inj₂ requested = selectedOutcome requested (select token requested observed) before

  selectedJournal : ∀ requested selected before changed reply → selectedOutcome requested selected before ≡ inj₂ (changed , reply) →
    Store.World.operations changed ≡ Store.World.operations before
  selectedJournal requested (inj₁ diagnostic) before changed reply ()
  selectedJournal requested (inj₂ (belief , value)) before changed reply accepted = B.journalUnchanged
    (Graph.BeliefValues.created belief) belief (just (Belief.Request.provenance requested)) value before changed reply accepted

  journal : ∀ observed token before changed reply → decide observed token before ≡ inj₂ (changed , reply) →
    Store.World.operations changed ≡ Store.World.operations before
  journal observed token before changed reply accepted with original token (Step.registration before)
  ... | inj₁ fault with accepted
  ... | ()
  journal observed token before changed reply accepted | inj₂ requested =
    selectedJournal requested (select token requested observed) before changed reply accepted

  module Final observed = Step.Admitted ℕ B.Diagnostic (λ token → token) Belief.publicationKey publicationDistinct
    (decide observed) (journal observed) admit

  finalPreservesFirst : ∀ observed token before →
    Store.lookupSaved (proj₁ (Final.execute observed token before)) token (Belief.ownerKey token) ≡
      Store.lookupSaved before token (Belief.ownerKey token)
  finalPreservesFirst observed token before with admit token (Step.registration before)
  ... | just _ = refl
  ... | nothing with Store.lookupCancellation before token
  ... | just _ = refl
  ... | nothing with Store.lookupSaved before token (Belief.publicationKey token) | Store.lookupSaved before token Step.resultKey
  ... | just _ | just _ = refl
  ... | just _ | nothing = refl
  ... | nothing | just _ = refl
  ... | nothing | nothing with decide observed token before in accepted
  ... | inj₁ _ = refl
  ... | inj₂ (changed , reply) = trans
    (Store.otherSavedAnswerPreserved (Final.Kernel.firstPublication observed token changed reply) token Step.resultKey reply
      token (Belief.ownerKey token) (λ same → Belief.ownerDistinct token (proj₂ same)))
    (trans (Store.otherSavedAnswerPreserved changed token (Belief.publicationKey token) reply token (Belief.ownerKey token)
      (λ same → Belief.phasesDifferent token (proj₂ same)))
      (Final.Kernel.changedLookup observed token before changed reply (Belief.ownerKey token) accepted))

  second : Packet → ℕ → Store.World → Store.World × Step.Result B.Diagnostic
  second observed token before with Store.lookupSaved before token (Belief.ownerKey token)
  ... | nothing = before , Step.needsRecovery
  ... | just _ = Final.execute observed token before

  secondStable : ∀ observed token before → second observed token (proj₁ (second observed token before)) ≡ second observed token before
  secondStable observed token before with Store.lookupSaved before token (Belief.ownerKey token) in saved
  ... | nothing rewrite saved = refl
  ... | just _ rewrite finalPreservesFirst observed token before | saved = Final.stable observed token before

  secondPhysical : ∀ observed token before → DB.Atomic before (proj₁ (second observed token before))
    (Step.receiptFor (proj₂ (second observed token before))) (proj₁ (second observed token before))
  secondPhysical observed token before with Store.lookupSaved before token (Belief.ownerKey token)
  ... | nothing = DB.abortedNone
  ... | just _ = Final.expectedPhysical observed token before

  module Run = Sequence.ObservedTwoPhases ℕ Belief.Allocation Packet B.Diagnostic first second
    firstStable secondStable firstPhysical secondPhysical allocate
    (λ token before → packet before (inj₁ (toList "Embedding preparation requires its actual backend response.")))

  publishedFirst : ∀ observed token before changed reply → decide observed token before ≡ inj₂ (changed , reply) →
    Store.lookupSaved (Final.Kernel.publication observed token changed reply) token (Belief.ownerKey token) ≡
      Store.lookupSaved before token (Belief.ownerKey token)
  publishedFirst observed token before changed reply accepted = trans
    (Store.otherSavedAnswerPreserved (Final.Kernel.firstPublication observed token changed reply) token Step.resultKey reply
      token (Belief.ownerKey token) (λ same → Belief.ownerDistinct token (proj₂ same)))
    (trans (Store.otherSavedAnswerPreserved changed token (Belief.publicationKey token) reply token (Belief.ownerKey token)
      (λ same → Belief.phasesDifferent token (proj₂ same)))
      (Final.Kernel.changedLookup observed token before changed reply (Belief.ownerKey token) accepted))

  prefixCompleteReplay : ∀ metadata token before saved next result →
    admit token (Step.registration before) ≡ nothing → Store.lookupCancellation before token ≡ nothing →
    Store.lookupSaved before token (Belief.ownerKey token) ≡ just saved →
    Store.lookupSaved before token (Belief.publicationKey token) ≡ just next →
    Store.lookupSaved before token Step.resultKey ≡ just result →
    first metadata token before ≡ (before , Step.done saved)
  prefixCompleteReplay metadata token before saved next result admitted active firstSaved nextSaved resultSaved
    rewrite admitted | active | firstSaved | nextSaved | resultSaved = refl

  prefixPendingReplay : ∀ metadata token before saved →
    admit token (Step.registration before) ≡ nothing → Store.lookupCancellation before token ≡ nothing →
    Store.lookupSaved before token (Belief.ownerKey token) ≡ just saved →
    Store.lookupSaved before token (Belief.publicationKey token) ≡ nothing →
    Store.lookupSaved before token Step.resultKey ≡ nothing → first metadata token before ≡ (before , Step.done saved)
  prefixPendingReplay metadata token before saved admitted active firstSaved nextSaved resultSaved
    rewrite admitted | active | firstSaved | nextSaved | resultSaved = refl

  firstFamily : ∀ wanted wantedFinal received token before →
    Σ Belief.Allocation (λ original → Σ Packet (λ final →
      Run.evaluate wanted wantedFinal token (proj₁ (first received token before)) ≡ Run.evaluate original final token before))
  firstFamily wanted final received token before with firstClassification received token before
  ... | inj₁ unchanged = wanted , final , cong (Run.evaluate wanted final token) unchanged
  ... | inj₂ (changed , reply , admitted , active , firstSaved , nextSaved , resultSaved , accepted) =
    received , final , trans
      (cong (Run.evaluate wanted final token) (cong proj₁ observed))
      (trans afterReplay (sym beforeReplay))
    where
    middle = O.Saved.Base.firstPublication received token changed reply
    observed = freshPrefix received token before changed reply admitted active firstSaved nextSaved resultSaved accepted
    publicationAdmitted = trans (cong (admit token) (O.Saved.keepsRegistration received token before changed reply accepted)) admitted
    publicationActive = trans (O.Saved.keepsCancellation received token before changed reply accepted) active
    readable = O.Saved.Base.firstReadable received token before changed reply accepted firstSaved
    noNext = trans (O.Saved.keepsNext received token before changed reply accepted) nextSaved
    noResult = O.Saved.Base.firstHasNoResult received token before changed reply accepted resultSaved
    replay = prefixPendingReplay wanted token middle reply publicationAdmitted publicationActive readable noNext noResult
    afterReplay = cong (λ pair → Run.remaining final token (proj₂ pair) (proj₁ pair)) replay
    beforeReplay = cong (λ pair → Run.remaining final token (proj₂ pair) (proj₁ pair)) observed

  secondCompleteReplay : ∀ observed token before saved next result →
    admit token (Step.registration before) ≡ nothing → Store.lookupCancellation before token ≡ nothing →
    Store.lookupSaved before token (Belief.ownerKey token) ≡ just saved →
    Store.lookupSaved before token (Belief.publicationKey token) ≡ just next →
    Store.lookupSaved before token Step.resultKey ≡ just result → second observed token before ≡ (before , Step.done next)
  secondCompleteReplay observed token before saved next result admitted active firstSaved nextSaved resultSaved
    rewrite firstSaved | admitted | active | nextSaved | resultSaved = refl

  secondFresh : ∀ observed token before saved changed reply →
    admit token (Step.registration before) ≡ nothing → Store.lookupCancellation before token ≡ nothing →
    Store.lookupSaved before token (Belief.ownerKey token) ≡ just saved →
    Store.lookupSaved before token (Belief.publicationKey token) ≡ nothing →
    Store.lookupSaved before token Step.resultKey ≡ nothing → decide observed token before ≡ inj₂ (changed , reply) →
    second observed token before ≡ (Final.Kernel.publication observed token changed reply , Step.done reply)
  secondFresh observed token before saved changed reply admitted active firstSaved nextSaved resultSaved accepted
    rewrite firstSaved | admitted | active | nextSaved | resultSaved | accepted = refl

  publishedEvaluation : ∀ initial wanted received token before changed reply saved →
    admit token (Step.registration before) ≡ nothing → Store.lookupCancellation before token ≡ nothing →
    Store.lookupSaved before token (Belief.ownerKey token) ≡ just saved →
    Store.lookupSaved before token (Belief.publicationKey token) ≡ nothing →
    Store.lookupSaved before token Step.resultKey ≡ nothing → decide received token before ≡ inj₂ (changed , reply) →
    Run.evaluate initial wanted token (Final.Kernel.publication received token changed reply) ≡
      (Final.Kernel.publication received token changed reply , Step.done reply)
  publishedEvaluation initial wanted received token before changed reply saved admitted active firstSaved secondAbsent resultAbsent accepted = trans
    (cong (λ result → Run.remaining wanted token (proj₂ result) (proj₁ result))
      (prefixCompleteReplay initial token published saved reply reply publicationAdmitted publicationActive
        publicationFirst publicationSecond publicationResult))
    (secondCompleteReplay wanted token published saved reply reply publicationAdmitted publicationActive
      publicationFirst publicationSecond publicationResult)
    where
    published = Final.Kernel.publication received token changed reply
    publicationAdmitted = trans (cong (admit token)
      (Final.Kernel.publicationKeepsRegistration received token before changed reply accepted)) admitted
    publicationActive = trans (Final.Kernel.publicationKeepsCancellation received token before changed reply accepted) active
    publicationFirst = trans (publishedFirst received token before changed reply accepted) firstSaved
    publicationSecond = Final.Kernel.publishedStepReadable received token before changed reply accepted secondAbsent
    publicationResult = Final.Kernel.publishedResultReadable received token before changed reply accepted resultAbsent

  originalEvaluation : ∀ initial received token before changed reply saved →
    admit token (Step.registration before) ≡ nothing → Store.lookupCancellation before token ≡ nothing →
    Store.lookupSaved before token (Belief.ownerKey token) ≡ just saved →
    Store.lookupSaved before token (Belief.publicationKey token) ≡ nothing →
    Store.lookupSaved before token Step.resultKey ≡ nothing → decide received token before ≡ inj₂ (changed , reply) →
    Run.evaluate initial received token before ≡ (Final.Kernel.publication received token changed reply , Step.done reply)
  originalEvaluation initial received token before changed reply saved admitted active firstSaved secondAbsent resultAbsent accepted = trans
    (cong (λ result → Run.remaining received token (proj₂ result) (proj₁ result))
      (prefixPendingReplay initial token before saved admitted active firstSaved secondAbsent resultAbsent))
    (secondFresh received token before saved changed reply admitted active firstSaved secondAbsent resultAbsent accepted)

  abstract
    observation : Belief.Allocation → Packet → ℕ → Store.World → Store.World × Run.Value
    observation = Run.evaluate
    observationDefinition : ∀ initial final token before → observation initial final token before ≡ Run.evaluate initial final token before
    observationDefinition initial final token before = refl

  secondFamilyObservation : ∀ initial wanted received token before → Σ Packet (λ original →
    observation initial wanted token (proj₁ (second received token before)) ≡ observation initial original token before)
  secondFamilyObservation initial wanted received token before with Store.lookupSaved before token (Belief.ownerKey token) in firstSaved
  ... | nothing = wanted , refl
  ... | just saved with admit token (Step.registration before) in admitted
  ... | just diagnostic = wanted , refl
  ... | nothing with Store.lookupCancellation before token in active
  ... | just cancelled = wanted , refl
  ... | nothing with Store.lookupSaved before token (Belief.publicationKey token) in secondSaved
    | Store.lookupSaved before token Step.resultKey in resultSaved
  ... | just _ | just _ = wanted , refl
  ... | just _ | nothing = wanted , refl
  ... | nothing | just _ = wanted , refl
  ... | nothing | nothing with decide received token before in accepted
  ... | inj₁ diagnostic = wanted , refl
  ... | inj₂ (changed , reply) = received , trans
    (observationDefinition initial wanted token (Final.Kernel.publication received token changed reply))
    (trans (publishedEvaluation initial wanted received token before changed reply saved admitted active firstSaved secondSaved resultSaved accepted)
      (trans (sym (originalEvaluation initial received token before changed reply saved admitted active firstSaved secondSaved resultSaved accepted))
        (sym (observationDefinition initial received token before))))

  secondFamily : ∀ initial wanted received token before → Σ Packet (λ original →
    Run.evaluate initial wanted token (proj₁ (second received token before)) ≡ Run.evaluate initial original token before)
  secondFamily initial wanted received token before with secondFamilyObservation initial wanted received token before
  ... | original , same = original , trans
    (sym (observationDefinition initial wanted token (proj₁ (second received token before))))
    (trans same (observationDefinition initial original token before))

  SelectedIntent : Belief.Request → Selection → Store.World → B.Outcome → Set
  SelectedIntent requested (inj₁ diagnostic) before outcome = outcome ≡ inj₁ diagnostic
  SelectedIntent requested (inj₂ (belief , value)) before outcome = B.Goal
    (Graph.BeliefValues.created belief) belief (just (Belief.Request.provenance requested)) value before outcome

  selectedMeaning : ∀ requested selected before → SelectedIntent requested selected before (selectedOutcome requested selected before)
  selectedMeaning requested (inj₁ diagnostic) before = refl
  selectedMeaning requested (inj₂ (belief , value)) before = proj₂ (B.checked
    (Graph.BeliefValues.created belief) belief (just (Belief.Request.provenance requested)) value before)

  FinalIntent : Packet → ℕ → Store.World → B.Outcome → Set
  FinalIntent observed token before outcome with original token (Step.registration before)
  ... | inj₁ fault = outcome ≡ inj₁ (B.requestFault fault)
  ... | inj₂ requested = SelectedIntent requested (select token requested observed) before outcome

  decisionMeaning : ∀ observed token before → FinalIntent observed token before (decide observed token before)
  decisionMeaning observed token before with original token (Step.registration before)
  ... | inj₁ fault = refl
  ... | inj₂ requested = selectedMeaning requested (select token requested observed) before

  FreshFinalGoal : Packet → ℕ → Store.World → Store.World → Run.Value → Set
  FreshFinalGoal observed token before after (Step.done reply) = Σ Store.World (λ changed →
    FinalIntent observed token before (inj₂ (changed , reply)) ×
      after ≡ Final.Kernel.publication observed token changed reply)
  FreshFinalGoal observed token before after (Step.needsInput diagnostic) = after ≡ before × FinalIntent observed token before (inj₁ diagnostic)
  FreshFinalGoal observed token before after _ = ⊥

  freshFinalMeaning : ∀ observed token before → FreshFinalGoal observed token before
    (proj₁ (Final.Kernel.fresh observed token before)) (proj₂ (Final.Kernel.fresh observed token before))
  freshFinalMeaning observed token before with decide observed token before in accepted
  ... | inj₁ diagnostic = refl , subst (FinalIntent observed token before) accepted (decisionMeaning observed token before)
  ... | inj₂ (changed , reply) = changed , subst (FinalIntent observed token before) accepted (decisionMeaning observed token before) , refl

  FinalGoal : Packet → ℕ → Store.World → Store.World → Run.Value → Set
  FinalGoal observed token before after reply with Store.lookupSaved before token (Belief.ownerKey token)
  ... | nothing = after ≡ before × reply ≡ Step.needsRecovery
  ... | just _ with admit token (Step.registration before)
  ... | just diagnostic = after ≡ before × reply ≡ Step.needsInput diagnostic
  ... | nothing with Store.lookupCancellation before token
  ... | just cancelled = after ≡ before × reply ≡ Step.cancelled cancelled
  ... | nothing with Store.lookupSaved before token (Belief.publicationKey token) | Store.lookupSaved before token Step.resultKey
  ... | just saved | just _ = after ≡ before × reply ≡ Step.done saved
  ... | just _ | nothing = after ≡ before × reply ≡ Step.needsRecovery
  ... | nothing | just _ = after ≡ before × reply ≡ Step.needsRecovery
  ... | nothing | nothing = FreshFinalGoal observed token before after reply

  secondMeaning : ∀ observed token before → FinalGoal observed token before
    (proj₁ (second observed token before)) (proj₂ (second observed token before))
  secondMeaning observed token before with Store.lookupSaved before token (Belief.ownerKey token)
  ... | nothing = refl , refl
  ... | just _ with admit token (Step.registration before)
  ... | just diagnostic = refl , refl
  ... | nothing with Store.lookupCancellation before token
  ... | just cancelled = refl , refl
  ... | nothing with Store.lookupSaved before token (Belief.publicationKey token) | Store.lookupSaved before token Step.resultKey
  ... | just _ | just _ = refl , refl
  ... | just _ | nothing = refl , refl
  ... | nothing | just _ = refl , refl
  ... | nothing | nothing = freshFinalMeaning observed token before

  ContinuationGoal : Packet → ℕ → Store.World → Run.Value → Store.World → Run.Value → Set
  ContinuationGoal observed token middle (Step.done _) after reply = FinalGoal observed token middle after reply
  ContinuationGoal observed token middle previous@(Step.needsInput _) after reply = after ≡ middle × reply ≡ previous
  ContinuationGoal observed token middle Step.needsRecovery after reply = after ≡ middle × reply ≡ Step.needsRecovery
  ContinuationGoal observed token middle previous@(Step.cancelled _) after reply = after ≡ middle × reply ≡ previous

  -- A successful fresh result fixes belief, vector, cited source list and
  -- provenance together, keeping weighted evidence and all unrelated fields.
  -- A dialog keeps the durable allocation prefix and no final publication.
  Goal : ℕ → Store.World → Store.World → Run.Value → Set
  Goal token before after reply = Σ Belief.Allocation (λ allocated → Σ Packet (λ observed →
    Σ Store.World (λ middle → Σ Run.Value (λ previous →
      O.Goal allocated token before middle previous × ContinuationGoal observed token middle previous after reply))))

  tailMeaning : ∀ observed token middle previous → ContinuationGoal observed token middle previous
    (proj₁ (Run.remaining observed token previous middle)) (proj₂ (Run.remaining observed token previous middle))
  tailMeaning observed token middle (Step.done _) = secondMeaning observed token middle
  tailMeaning observed token middle (Step.needsInput _) = refl , refl
  tailMeaning observed token middle Step.needsRecovery = refl , refl
  tailMeaning observed token middle (Step.cancelled _) = refl , refl

  meaning : ∀ initial final token before → Goal token before
    (proj₁ (Run.evaluate initial final token before)) (proj₂ (Run.evaluate initial final token before))
  meaning initial final token before = initial , final , proj₁ (first initial token before) , proj₂ (first initial token before) ,
    O.meaning initial token before , tailMeaning final token (proj₁ (first initial token before)) (proj₂ (first initial token before))

  private
    module Certified = Run.Certified firstFamily secondFamily Goal meaning

  -- The only public input is the reserved token. Snapshot/vector observations
  -- are constructed by these effects and retained in the semantic receipt.
  module Public (coreConfiguration : Config.Config) where
    configuration : Maybe Config.Embeddings
    configuration = Config.Config.embed coreConfiguration
    inputText : ℕ → Store.World → Maybe Text
    inputText token snapshot with original token (Step.registration snapshot)
    ... | inj₁ _ = nothing
    ... | inj₂ requested with owner token (Store.World.embeddingOwners snapshot)
    ... | nothing = nothing
    ... | just row with Belief.initial requested (allocation row)
    ... | nothing = nothing
    ... | just belief with Embedding.selectSupport belief snapshot (Belief.Request.grounding requested)
    ... | inj₁ _ = nothing
    ... | inj₂ [] = nothing
    ... | inj₂ (_ ∷ _) = just (Graph.BeliefValues.content belief)

    module Fields = Project.Registered
    identityMatches : Config.Embeddings → Wire.Value → Bool
    identityMatches cfg with Config.Embeddings.backend cfg
    ... | Config.local = Belief.ProviderSettings.local
    ... | Config.voyage = Fields.fields (toList "backend" ∷ toList "model" ∷ toList "input_type" ∷ toList "truncation" ∷ []) λ view →
      Data.Bool._∧_ (Fields.fieldText (toList "voyage") (view (toList "backend")))
      (Data.Bool._∧_ (Fields.fieldText (Config.Embeddings.model cfg) (view (toList "model")))
      (Data.Bool._∧_ (Fields.fieldText (toList "document") (view (toList "input_type"))) (Fields.fieldFalse (view (toList "truncation")))))
    ... | Config.openai = Fields.fields (toList "backend" ∷ toList "model" ∷ []) λ view →
      Data.Bool._∧_ (Fields.fieldText (toList "openai") (view (toList "backend")))
        (Fields.fieldText (Config.Embeddings.model cfg) (view (toList "model")))

    configuredIdentity : Config.Embeddings → Maybe Wire.Value → Bool
    configuredIdentity cfg nothing = false
    configuredIdentity cfg (just value) = identityMatches cfg value

    settingsMatch : Config.Embeddings → ℕ → Store.World → Bool
    settingsMatch cfg token snapshot with Fields.binding token (Store.OperationTables.bindings (Store.World.operations snapshot))
    ... | nothing = false
    ... | just bound = Fields.fields (toList "embeddings" ∷ [])
      (λ view → configuredIdentity cfg (view (toList "embeddings"))) (Store.BindingRow.settings bound)

    data Effect : Set where
      reserve : ℕ → Effect
      readSources : ℕ → Effect
      embed : ℕ → Config.Embeddings → Text → Effect
      publish : ℕ → Packet → Effect

    Reply : Effect → Set
    Reply (reserve _) = Belief.Allocation × Run.Value
    Reply (readSources _) = Text ⊎ Store.World
    Reply (embed _ _ _) = Text ⊎ List Store.Vector
    Reply (publish _ _) = Run.Value
    module E = Effects.Protocol Effect Reply

    record Result : Set where
      constructor completed
      field value : Run.Value; transcript : List E.Event

    finish : ℕ → List E.Event → Packet → E.Script Result
    finish token previous observed = E.ask (publish token observed) (λ value →
      E.done (completed value (previous ++ ((publish token observed , value) ∷ []))))

    unprepared : Text
    unprepared = toList "Preparation cannot proceed with the original source or owner; read the exact correction and open the user dialog. No belief was stored."

    afterInput : ℕ → List E.Event → Store.World → Maybe Text → E.Script Result
    afterInput token previous snapshot nothing = finish token previous (packet snapshot (inj₁ unprepared))
    afterInput token previous snapshot (just content) with configuration
    ... | nothing = finish token previous (packet snapshot (inj₁
      (toList "Embedding is not configured. Open the user dialog to configure it or cancel this unfinished operation; no belief was stored.")))
    ... | just cfg with settingsMatch cfg token snapshot
    ... | false = finish token previous (packet snapshot (inj₁
      (toList "The configured embedding backend differs from this token's original settings. Read its binding and outcome, then ask the user before cancellation and a corrected reservation. No belief was stored.")))
    ... | true = E.ask (embed token cfg content) (λ response → finish token
      (previous ++ ((embed token cfg content , response) ∷ [])) (packet snapshot response))

    afterSnapshot : ℕ → List E.Event → Text ⊎ Store.World → E.Script Result
    afterSnapshot token previous (inj₁ reason) = finish token previous (sourceUnavailable reason)
    afterSnapshot token previous (inj₂ snapshot) with Store.lookupSaved snapshot token (Belief.publicationKey token)
      | Store.lookupSaved snapshot token Step.resultKey
    ... | nothing | nothing = afterInput token previous snapshot (inputText token snapshot)
    ... | just _ | _ = finish token previous (packet snapshot (inj₁ unprepared))
    ... | nothing | just _ = finish token previous (packet snapshot (inj₁ unprepared))

    afterOwner : ℕ → List E.Event → Run.Value → E.Script Result
    afterOwner token previous (Step.done _) = E.ask (readSources token) (λ observed →
      afterSnapshot token (previous ++ ((readSources token , observed) ∷ [])) observed)
    afterOwner token previous value@(Step.needsInput _) = E.done (completed value previous)
    afterOwner token previous Step.needsRecovery = E.done (completed Step.needsRecovery previous)
    afterOwner token previous value@(Step.cancelled _) = E.done (completed value previous)

    script : ℕ → E.Script Result
    script token = E.ask (reserve token) (λ observed → afterOwner token ((reserve token , observed) ∷ []) (proj₂ observed))

    Atomic : Store.World → (effect : Effect) → Reply effect → Store.World → Set
    Atomic before (reserve token) observed after = Run.Atomic before (Run.prefix token) observed after
    Atomic before (readSources token) (inj₁ reason) after = after ≡ before
    Atomic before (readSources token) (inj₂ snapshot) after = snapshot ≡ before × after ≡ before
    Atomic before (embed token cfg content) reply after = after ≡ before
    Atomic before (publish token observed) reply after = Run.Atomic before (Run.finish token) (observed , reply) after
    module X = Recovery.Execution Store.World Effect Reply Atomic

    -- A completed publication is replayed through its real owner/read/final
    -- path. Its saved answers, rather than a newly prepared vector, determine
    -- the reply. The caller derives these journal facts from the actual cut.
    cachedReplay : ∀ token current ownerAnswer raw →
      admit token (Step.registration current) ≡ nothing →
      Store.lookupCancellation current token ≡ nothing →
      Store.lookupSaved current token (Belief.ownerKey token) ≡ just ownerAnswer →
      Store.lookupSaved current token (Belief.publicationKey token) ≡ just raw →
      Store.lookupSaved current token Step.resultKey ≡ just raw →
      Σ Result (λ reply → X.Completed (script token) current current reply ×
        Result.value reply ≡ Step.done raw)
    cachedReplay token current ownerAnswer raw admitted active ownerSaved finalSaved resultSaved =
      answer , X.completed events control physical , refl
      where
      metadata = allocate token current
      observed = packet current (inj₁ unprepared)
      prefix = (reserve token , (metadata , Step.done ownerAnswer)) ∷ []
      sources = prefix ++ ((readSources token , inj₂ current) ∷ [])
      events = sources ++ ((publish token observed , Step.done raw) ∷ [])
      answer = completed (Step.done raw) events
      ownerEquation = prefixCompleteReplay metadata token current ownerAnswer raw raw
        admitted active ownerSaved finalSaved resultSaved
      finalEquation = secondCompleteReplay observed token current ownerAnswer raw raw
        admitted active ownerSaved finalSaved resultSaved
      ownerPhysical : Atomic current (reserve token) (metadata , Step.done ownerAnswer) current
      ownerPhysical rewrite ownerEquation = refl , DB.committedAll
      finalPhysical : Atomic current (publish token observed) (Step.done raw) current
      finalPhysical rewrite finalEquation = refl , DB.committedAll
      snapshotControl : E.Runs (afterSnapshot token sources (inj₂ current))
        ((publish token observed , Step.done raw) ∷ []) answer
      snapshotControl rewrite finalSaved = E.replied _ _ _ (E.returned _)
      control : E.Runs (script token) events answer
      control = E.replied _ _ _ (E.replied _ _ _ snapshotControl)
      physical : X.Changes current events current
      physical = X.changed _ _ _ _ ownerPhysical
        (X.changed _ _ _ _ (refl , refl)
          (X.changed _ _ _ _ finalPhysical (X.unchanged _)))

    data Owned (token : ℕ) : Effect → Set where
      ownerOwned : Owned token (reserve token)
      sourcesOwned : Owned token (readSources token)
      embedOwned : ∀ cfg content → Owned token (embed token cfg content)
      publishOwned : ∀ observed → Owned token (publish token observed)

    data Scoped (token : ℕ) : E.Script Result → Set where
      returned : ∀ value → Scoped token (E.done value)
      asked : ∀ effect continuation → Owned token effect →
        (∀ reply → Scoped token (continuation reply)) → Scoped token (E.ask effect continuation)

    finishScoped : ∀ token previous observed → Scoped token (finish token previous observed)
    finishScoped token previous observed = asked _ _ (publishOwned observed) (λ value → returned _)
    inputScoped : ∀ token previous snapshot input → Scoped token (afterInput token previous snapshot input)
    inputScoped token previous snapshot nothing = finishScoped _ _ _
    inputScoped token previous snapshot (just content) with configuration
    ... | nothing = finishScoped _ _ _
    ... | just cfg with settingsMatch cfg token snapshot
    ... | false = finishScoped _ _ _
    ... | true = asked _ _ (embedOwned cfg content) (λ response → finishScoped _ _ _)
    snapshotScoped : ∀ token previous observation → Scoped token (afterSnapshot token previous observation)
    snapshotScoped token previous (inj₁ reason) = finishScoped _ _ _
    snapshotScoped token previous (inj₂ snapshot) with Store.lookupSaved snapshot token (Belief.publicationKey token)
      | Store.lookupSaved snapshot token Step.resultKey
    ... | nothing | nothing = inputScoped token previous snapshot (inputText token snapshot)
    ... | just _ | _ = finishScoped _ _ _
    ... | nothing | just _ = finishScoped _ _ _
    ownerScoped : ∀ token previous value → Scoped token (afterOwner token previous value)
    ownerScoped token previous (Step.done _) = asked _ _ sourcesOwned (λ snapshot →
      snapshotScoped token (previous ++ ((readSources token , snapshot) ∷ [])) snapshot)
    ownerScoped token previous (Step.needsInput _) = returned _
    ownerScoped token previous Step.needsRecovery = returned _
    ownerScoped token previous (Step.cancelled _) = returned _
    scriptScoped : ∀ token → Scoped token (script token)
    scriptScoped token = asked _ _ ownerOwned (λ observed → ownerScoped _ _ _)

    prefixScoped : ∀ token program events residual → Scoped token program → E.Prefix program events residual →
      All (λ event → Owned token (proj₁ event)) events × Scoped token residual
    prefixScoped token program [] .program scoped (E.stopped _) = [] , scoped
    prefixScoped token .(E.ask effect continuation) .((effect , reply) ∷ events) residual
      (asked effect continuation own later) (E.replied _ _ reply {events} rest)
      with prefixScoped token (continuation reply) events residual (later reply) rest
    ... | owners , scoped = (own ∷ owners) , scoped
    activeOwned : ∀ token effect continuation → Scoped token (E.ask effect continuation) → Owned token effect
    activeOwned token effect continuation (asked .effect .continuation own later) = own

    -- These are computed journal facts, established by the physical prefix.
    -- In particular a new final answer must come from the paired publication.
    ReplayFacts : ℕ → Store.World → Set
    ReplayFacts token current = admit token (Step.registration current) ≡ nothing ×
      Store.lookupCancellation current token ≡ nothing ×
      (∀ raw → Store.lookupSaved current token Step.resultKey ≡ just raw →
        Σ Wire.Value (λ ownerAnswer →
          Store.lookupSaved current token (Belief.ownerKey token) ≡ just ownerAnswer ×
          Store.lookupSaved current token (Belief.publicationKey token) ≡ just raw))

    noSavedAnswer : ∀ {raw : Wire.Value} → nothing ≡ just raw → ⊥
    noSavedAnswer ()
    sameSavedAnswer : ∀ {left right : Wire.Value} → just left ≡ just right → left ≡ right
    sameSavedAnswer refl = refl

    firstKeepsReplay : ∀ metadata token current → ReplayFacts token current →
      ReplayFacts token (proj₁ (first metadata token current))
    firstKeepsReplay metadata token current old with firstClassification metadata token current
    ... | inj₁ unchanged = subst (ReplayFacts token) (sym unchanged) old
    ... | inj₂ (changed , reply , admitted , active , ownerAbsent , finalAbsent , resultAbsent , accepted) =
      subst (ReplayFacts token) (sym (cong proj₁ published))
        (trans (cong (admit token) (O.Saved.keepsRegistration metadata token current changed reply accepted)) admitted ,
         trans (O.Saved.keepsCancellation metadata token current changed reply accepted) active ,
         λ raw known → ⊥-elim (noSavedAnswer (trans (sym noResult) known)))
      where
      published = freshPrefix metadata token current changed reply admitted active ownerAbsent finalAbsent resultAbsent accepted
      noResult = O.Saved.Base.firstHasNoResult metadata token current changed reply accepted resultAbsent

    SecondPublication : Packet → ℕ → Store.World → Set
    SecondPublication observed token current = Σ Wire.Value (λ ownerAnswer →
      Σ Store.World (λ changed → Σ Wire.Value (λ reply →
        admit token (Step.registration current) ≡ nothing ×
        Store.lookupCancellation current token ≡ nothing ×
        Store.lookupSaved current token (Belief.ownerKey token) ≡ just ownerAnswer ×
        Store.lookupSaved current token (Belief.publicationKey token) ≡ nothing ×
        Store.lookupSaved current token Step.resultKey ≡ nothing ×
        decide observed token current ≡ inj₂ (changed , reply))))

    secondClassification : ∀ observed token current →
      (proj₁ (second observed token current) ≡ current) ⊎ SecondPublication observed token current
    secondClassification observed token current with Store.lookupSaved current token (Belief.ownerKey token) in ownerSaved
    ... | nothing = inj₁ refl
    ... | just ownerAnswer with admit token (Step.registration current) in admitted
    ... | just _ = inj₁ refl
    ... | nothing with Store.lookupCancellation current token in active
    ... | just _ = inj₁ refl
    ... | nothing with Store.lookupSaved current token (Belief.publicationKey token) in finalSaved
      | Store.lookupSaved current token Step.resultKey in resultSaved
    ... | just _ | just _ = inj₁ refl
    ... | just _ | nothing = inj₁ refl
    ... | nothing | just _ = inj₁ refl
    ... | nothing | nothing with decide observed token current in accepted
    ... | inj₁ _ = inj₁ refl
    ... | inj₂ (changed , reply) = inj₂
      (ownerAnswer , changed , reply , refl , refl , refl , refl , refl , refl)

    secondKeepsReplay : ∀ observed token current → ReplayFacts token current →
      ReplayFacts token (proj₁ (second observed token current))
    secondKeepsReplay observed token current old with secondClassification observed token current
    ... | inj₁ unchanged = subst (ReplayFacts token) (sym unchanged) old
    ... | inj₂ (ownerAnswer , changed , reply , admitted , active , ownerSaved , finalAbsent , resultAbsent , accepted) =
      subst (ReplayFacts token) (sym (cong proj₁ published))
        (trans (cong (admit token) (Final.Kernel.publicationKeepsRegistration observed token current changed reply accepted)) admitted ,
         trans (Final.Kernel.publicationKeepsCancellation observed token current changed reply accepted) active ,
         λ raw known → ownerAnswer , trans (publishedFirst observed token current changed reply accepted) ownerSaved ,
           trans finalReadable (cong just (sameSavedAnswer (trans (sym resultReadable) known))))
      where
      published = secondFresh observed token current ownerAnswer changed reply admitted active ownerSaved finalAbsent resultAbsent accepted
      finalReadable = Final.Kernel.publishedStepReadable observed token current changed reply accepted finalAbsent
      resultReadable = Final.Kernel.publishedResultReadable observed token current changed reply accepted resultAbsent

    atomicKeepsReplay : ∀ token before after effect reply → Owned token effect →
      Atomic before effect reply after → ReplayFacts token before → ReplayFacts token after
    atomicKeepsReplay token before after .(reserve token) (metadata , reply) ownerOwned (known , physical) old =
      DB.invariantPreserved (ReplayFacts token) physical old (firstKeepsReplay metadata token before old)
    atomicKeepsReplay token before .before .(readSources token) (inj₁ reason) sourcesOwned refl old = old
    atomicKeepsReplay token before .before .(readSources token) (inj₂ .before) sourcesOwned (refl , refl) old = old
    atomicKeepsReplay token before .before .(embed token cfg content) reply (embedOwned cfg content) refl old = old
    atomicKeepsReplay token before after .(publish token observed) reply (publishOwned observed) (known , physical) old =
      DB.invariantPreserved (ReplayFacts token) physical old (secondKeepsReplay observed token before old)

    changesKeepReplay : ∀ token before events after → All (λ event → Owned token (proj₁ event)) events →
      X.Changes before events after → ReplayFacts token before → ReplayFacts token after
    changesKeepReplay token before [] .before [] (X.unchanged _) old = old
    changesKeepReplay token before ((effect , reply) ∷ events) after (own ∷ owners)
      (X.changed _ _ _ middle physical rest) old = changesKeepReplay token middle events after owners rest
        (atomicKeepsReplay token before middle effect reply own physical old)

    interruptedKeepsReplay : ∀ token initial current → X.Interrupted (script token) initial current →
      ReplayFacts token initial → ReplayFacts token current
    interruptedKeepsReplay token initial current (X.atPrefix events residual .current prefix physical) old =
      changesKeepReplay token initial events current
        (proj₁ (prefixScoped token (script token) events residual (scriptScoped token) prefix)) physical old
    interruptedKeepsReplay token initial after
      (X.beforeReply events effect continuation current reply .after prefix physical active) old
      with prefixScoped token (script token) events (E.ask effect continuation) (scriptScoped token) prefix
    ... | owners , residual = atomicKeepsReplay token current after effect reply
      (activeOwned token effect continuation residual) active
      (changesKeepReplay token initial events current owners physical old)

    cachedReplayAfterCut : ∀ token initial current raw →
      admit token (Step.registration initial) ≡ nothing →
      Store.lookupCancellation initial token ≡ nothing →
      Store.lookupSaved initial token Step.resultKey ≡ nothing →
      X.Interrupted (script token) initial current →
      Store.lookupSaved current token Step.resultKey ≡ just raw →
      Σ Result (λ reply → X.Completed (script token) current current reply ×
        Result.value reply ≡ Step.done raw)
    cachedReplayAfterCut token initial current raw admitted active absent cut known
      with interruptedKeepsReplay token initial current cut
        (admitted , active , λ value saved → ⊥-elim (noSavedAnswer (trans (sym absent) saved)))
    ... | currentAdmitted , currentActive , paired with paired raw known
    ... | ownerAnswer , ownerSaved , finalSaved = cachedReplay token current ownerAnswer raw
      currentAdmitted currentActive ownerSaved finalSaved known

    atomicInvariant : ∀ token initial before after effect reply → Owned token effect →
      Atomic before effect reply after → Certified.Invariant token initial before → Certified.Invariant token initial after
    atomicInvariant token initial before after .(reserve token) observed ownerOwned physical invariant =
      Certified.atomicInvariant token initial before after (Run.prefix token) observed Run.firstOwned physical invariant
    atomicInvariant token initial before .before .(readSources token) (inj₁ reason) sourcesOwned refl invariant = invariant
    atomicInvariant token initial before .before .(readSources token) (inj₂ .before) sourcesOwned (refl , refl) invariant = invariant
    atomicInvariant token initial before .before .(embed token cfg content) reply (embedOwned cfg content) refl invariant = invariant
    atomicInvariant token initial before after .(publish token observed) reply (publishOwned observed) physical invariant =
      Certified.atomicInvariant token initial before after (Run.finish token) (observed , reply) Run.secondOwned physical invariant

    changesInvariant : ∀ token initial before events after → All (λ event → Owned token (proj₁ event)) events →
      X.Changes before events after → Certified.Invariant token initial before → Certified.Invariant token initial after
    changesInvariant token initial before [] .before [] (X.unchanged _) old = old
    changesInvariant token initial before ((effect , reply) ∷ events) after (own ∷ owners)
      (X.changed _ _ _ middle physical rest) old = changesInvariant token initial middle events after owners rest
        (atomicInvariant token initial before middle effect reply own physical old)

    interruptedInvariant : ∀ token initial interrupted → X.Interrupted (script token) initial interrupted → Certified.Invariant token initial interrupted
    interruptedInvariant token initial interrupted (X.atPrefix events residual .interrupted prefix physical) =
      changesInvariant token initial initial events interrupted
        (proj₁ (prefixScoped token (script token) events residual (scriptScoped token) prefix)) physical
        (λ first final → first , final , refl)
    interruptedInvariant token initial interrupted
      (X.beforeReply events effect continuation current reply .interrupted prefix physical active)
      with prefixScoped token (script token) events (E.ask effect continuation) (scriptScoped token) prefix
    ... | owners , residual = atomicInvariant token initial current interrupted effect reply
      (activeOwned token effect continuation residual) active
      (changesInvariant token initial initial events current owners physical (λ first final → first , final , refl))

    finishObservation : ∀ token previous observed before after result events →
      E.Runs (finish token previous observed) events result → X.Changes before events after →
      (after , Result.value result) ≡ second observed token before
    finishObservation token previous observed before after ._ ._
      (E.replied _ _ reply (E.returned _)) (X.changed _ _ _ _ physical (X.unchanged _)) =
      Run.Second.atomicObservation observed token before after reply physical

    inputObservation : ∀ token previous snapshot input before after result events →
      E.Runs (afterInput token previous snapshot input) events result → X.Changes before events after →
      Σ Packet (λ observed → (after , Result.value result) ≡ second observed token before)
    inputObservation token previous snapshot nothing before after result events execution physical = _ ,
      finishObservation token previous _ before after result events execution physical
    inputObservation token previous snapshot (just content) before after result events execution physical with configuration
    ... | nothing = _ , finishObservation token previous _ before after result events execution physical
    ... | just cfg with settingsMatch cfg token snapshot
    ... | false = _ , finishObservation token previous _ before after result events execution physical
    inputObservation token previous snapshot (just content) before after result ._
      (E.replied _ _ response execution) (X.changed _ _ _ .before refl physical) | just cfg | true =
      packet snapshot response , finishObservation token _ (packet snapshot response) before after result _ execution physical

    snapshotObservation : ∀ token previous observation before after result events →
      E.Runs (afterSnapshot token previous observation) events result → X.Changes before events after →
      Σ Packet (λ observed → (after , Result.value result) ≡ second observed token before)
    snapshotObservation token previous (inj₁ reason) before after result events execution physical = _ ,
      finishObservation token previous _ before after result events execution physical
    snapshotObservation token previous (inj₂ snapshot) before after result events execution physical
      with Store.lookupSaved snapshot token (Belief.publicationKey token) | Store.lookupSaved snapshot token Step.resultKey
    ... | nothing | nothing = inputObservation token previous snapshot (inputText token snapshot) before after result events execution physical
    ... | just _ | _ = _ , finishObservation token previous _ before after result events execution physical
    ... | nothing | just _ = _ , finishObservation token previous _ before after result events execution physical

    sourceReadUnchanged : ∀ token before reply after → Atomic before (readSources token) reply after → after ≡ before
    sourceReadUnchanged token before (inj₁ reason) after physical = physical
    sourceReadUnchanged token before (inj₂ snapshot) after physical = proj₂ physical

    tailObservation : ∀ token previous value before after result events →
      E.Runs (afterOwner token previous value) events result → X.Changes before events after →
      Σ Packet (λ observed → (after , Result.value result) ≡ Run.remaining observed token value before)
    tailObservation token previous (Step.done _) before after result ._
      (E.replied _ _ snapshot execution) (X.changed _ _ _ middle read physical)
      with snapshotObservation token _ snapshot middle after result _ execution physical
    ... | observed , same = observed , trans same
      (cong (second observed token) (sourceReadUnchanged token before snapshot middle read))
    tailObservation token previous (Step.needsInput diagnostic) before .before ._ .[] (E.returned _) (X.unchanged _) = sourceUnavailable [] , refl
    tailObservation token previous Step.needsRecovery before .before ._ .[] (E.returned _) (X.unchanged _) = sourceUnavailable [] , refl
    tailObservation token previous (Step.cancelled cancelled) before .before ._ .[] (E.returned _) (X.unchanged _) = sourceUnavailable [] , refl

    completedObservation : ∀ token before after result → X.Completed (script token) before after result →
      Σ Belief.Allocation (λ metadata → Σ Packet (λ observed →
        (after , Result.value result) ≡ Run.evaluate metadata observed token before))
    completedObservation token before after result
      (X.completed _ (E.replied _ _ (metadata , previous) execution) (X.changed _ _ _ middle physical rest))
      with tailObservation token _ previous middle after result _ execution rest
    ... | observed , same = metadata , observed , trans same
      (cong (λ pair → Run.remaining observed token (proj₂ pair) (proj₁ pair))
        (Run.First.atomicObservation metadata token before middle previous physical))

    PublicGoal : ℕ → Store.World → Store.World → Result → Set
    PublicGoal token before after result = Goal token before after (Result.value result)

    converges : ∀ token initial interrupted after result → X.Interrupted (script token) initial interrupted →
      X.Completed (script token) interrupted after result → PublicGoal token initial after result
    converges token initial interrupted after result crash completion
      with completedObservation token interrupted after result completion
    ... | metadata , observed , same with interruptedInvariant token initial interrupted crash metadata observed
    ... | original , final , retained = subst
      (λ pair → Goal token initial (proj₁ pair) (proj₂ pair)) (sym (trans same retained)) (meaning original final token initial)

    finishProgress : ∀ token previous observed before → Σ Store.World (λ after → Σ Result (λ result →
      X.Completed (finish token previous observed) before after result))
    finishProgress token previous observed before = proj₁ proposed , result , X.completed
      ((publish token observed , proj₂ proposed) ∷ []) (E.replied _ _ _ (E.returned _))
      (X.changed before _ _ _ (refl , secondPhysical observed token before) (X.unchanged _))
      where
      proposed = second observed token before
      result = completed (proj₂ proposed) (previous ++ ((publish token observed , proj₂ proposed) ∷ []))

    inputProgress : ∀ token previous snapshot input before → Σ Store.World (λ after → Σ Result (λ result →
      X.Completed (afterInput token previous snapshot input) before after result))
    inputProgress token previous snapshot nothing before = finishProgress _ _ _ _
    inputProgress token previous snapshot (just content) before with configuration
    ... | nothing = finishProgress _ _ _ _
    ... | just cfg with settingsMatch cfg token snapshot
    ... | false = finishProgress _ _ _ _
    ... | true with finishProgress token (previous ++ ((embed token cfg content , inj₁ []) ∷ [])) (packet snapshot (inj₁ [])) before
    ... | after , result , X.completed events execution physical = after , result , X.completed
      ((embed token cfg content , inj₁ []) ∷ events) (E.replied _ _ _ execution)
      (X.changed before _ _ before refl physical)

    snapshotProgress : ∀ token previous observation before → Σ Store.World (λ after → Σ Result (λ result →
      X.Completed (afterSnapshot token previous observation) before after result))
    snapshotProgress token previous (inj₁ reason) before = finishProgress _ _ _ _
    snapshotProgress token previous (inj₂ snapshot) before with Store.lookupSaved snapshot token (Belief.publicationKey token)
      | Store.lookupSaved snapshot token Step.resultKey
    ... | nothing | nothing = inputProgress token previous snapshot (inputText token snapshot) before
    ... | just _ | _ = finishProgress _ _ _ _
    ... | nothing | just _ = finishProgress _ _ _ _

    ownerProgress : ∀ token previous value before → Σ Store.World (λ after → Σ Result (λ result →
      X.Completed (afterOwner token previous value) before after result))
    ownerProgress token previous (Step.done _) before with snapshotProgress token
      (previous ++ ((readSources token , inj₂ before) ∷ [])) (inj₂ before) before
    ... | after , result , X.completed events execution physical = after , result , X.completed
      ((readSources token , inj₂ before) ∷ events) (E.replied _ _ _ execution)
      (X.changed before _ _ before (refl , refl) physical)
    ownerProgress token previous (Step.needsInput diagnostic) before = before , completed (Step.needsInput diagnostic) previous ,
      X.completed [] (E.returned _) (X.unchanged _)
    ownerProgress token previous Step.needsRecovery before = before , completed Step.needsRecovery previous ,
      X.completed [] (E.returned _) (X.unchanged _)
    ownerProgress token previous (Step.cancelled cancelled) before = before , completed (Step.cancelled cancelled) previous ,
      X.completed [] (E.returned _) (X.unchanged _)

    -- Existence of an allowed external response does not assert provider
    -- success or determinism, and introduces no timeout or retry ceiling.
    progress : ∀ token before → Σ Store.World (λ after → Σ Result (λ result → X.Completed (script token) before after result))
    progress token before with allocate token before
    ... | metadata with ownerProgress token ((reserve token , (metadata , proj₂ (first metadata token before))) ∷ [])
      (proj₂ (first metadata token before)) (proj₁ (first metadata token before))
    ... | after , result , X.completed events execution physical = after , result , X.completed
      ((reserve token , (metadata , proj₂ (first metadata token before))) ∷ events) (E.replied _ _ _ execution)
      (X.changed before _ _ _ (refl , firstPhysical metadata token before) physical)

    finishTranscript : ∀ token previous observed events result → E.Runs (finish token previous observed) events result →
      previous ++ events ≡ Result.transcript result
    finishTranscript token previous observed ._ ._ (E.replied _ _ value (E.returned _)) = refl

    inputTranscript : ∀ token previous snapshot input events result → E.Runs (afterInput token previous snapshot input) events result →
      previous ++ events ≡ Result.transcript result
    inputTranscript token previous snapshot nothing events result execution = finishTranscript _ _ _ _ _ execution
    inputTranscript token previous snapshot (just content) events result execution with configuration
    ... | nothing = finishTranscript _ _ _ _ _ execution
    ... | just cfg with settingsMatch cfg token snapshot
    ... | false = finishTranscript _ _ _ _ _ execution
    inputTranscript token previous snapshot (just content) ._ result (E.replied _ _ response {events} execution) | just cfg | true =
      trans (sym (Lists.++-assoc previous ((embed token cfg content , response) ∷ []) events))
        (finishTranscript _ _ _ _ _ execution)

    snapshotTranscript : ∀ token previous observation events result → E.Runs (afterSnapshot token previous observation) events result →
      previous ++ events ≡ Result.transcript result
    snapshotTranscript token previous (inj₁ reason) events result execution = finishTranscript _ _ _ _ _ execution
    snapshotTranscript token previous (inj₂ snapshot) events result execution with Store.lookupSaved snapshot token (Belief.publicationKey token)
      | Store.lookupSaved snapshot token Step.resultKey
    ... | nothing | nothing = inputTranscript token previous snapshot (inputText token snapshot) events result execution
    ... | just _ | _ = finishTranscript _ _ _ _ _ execution
    ... | nothing | just _ = finishTranscript _ _ _ _ _ execution

    ownerTranscript : ∀ token previous value events result → E.Runs (afterOwner token previous value) events result →
      previous ++ events ≡ Result.transcript result
    ownerTranscript token previous (Step.done _) ._ result (E.replied _ _ observed {events} execution) =
      trans (sym (Lists.++-assoc previous ((readSources token , observed) ∷ []) events))
        (snapshotTranscript token (previous ++ ((readSources token , observed) ∷ [])) observed events result execution)
    ownerTranscript token previous (Step.needsInput _) .[] ._ (E.returned _) = Lists.++-identityʳ previous
    ownerTranscript token previous Step.needsRecovery .[] ._ (E.returned _) = Lists.++-identityʳ previous
    ownerTranscript token previous (Step.cancelled _) .[] ._ (E.returned _) = Lists.++-identityʳ previous

    -- The receipt records exactly the public execution's events. In
    -- particular its vector is the reply to embed(token, configured backend,
    -- original complete content), following that execution's source read.
    actualReceipts : ∀ token before after result (execution : X.Completed (script token) before after result) →
      X.Completed.events execution ≡ Result.transcript result
    actualReceipts token before after result (X.completed _ (E.replied _ _ observed execution) physical) =
      ownerTranscript token ((reserve token , observed) ∷ []) (proj₂ observed) _ result execution

    -- Assembly must retain this complete certificate, including observes;
    -- projecting a weaker durable-only operation would lose receipt binding.
    record Operation : Set₁ where
      field
        recovers : ∀ token initial interrupted after result → X.Interrupted (script token) initial interrupted →
          X.Completed (script token) interrupted after result → PublicGoal token initial after result
        progresses : ∀ token before → Σ Store.World (λ after → Σ Result (λ result → X.Completed (script token) before after result))
        observes : ∀ token before after result (execution : X.Completed (script token) before after result) →
          X.Completed.events execution ≡ Result.transcript result

    fullOperation : Operation
    fullOperation = record { recovers = converges; progresses = progress; observes = actualReceipts }

    toRecoverable : Operation → Recovery.RecoverableFor Store.World ℕ Result PublicGoal
    toRecoverable certificate = record
      { Effect = Effect; Reply = Reply; script = script; Atomic = Atomic
      ; converges = Operation.recovers certificate; progress = Operation.progresses certificate }
