{-# OPTIONS --safe #-}
-- Dependency-ordered acyclic inference and the remaining cyclic iteration.
-- Standard Float supplies arithmetic;
-- this module specifies Mimir's iteration order, fixed priors, clamped seed,
-- external parents, convergence test and durable-update selection.
module Mimir.PosteriorComputation where

open import Data.Float.Base using (Float; _+_; _-_; _*_; _÷_; _<ᵇ_; _≤ᵇ_; isNaN)
open import Data.Bool using (Bool; true; false; _∨_; _∧_; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≟_; _≤?_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no; does)
open import Relation.Nullary.Decidable.Core using (_×-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; cong; subst)
import Mimir.ReviewSchema as Review
import Mimir.AssessmentScores as Scores
open import Mimir.SourceReview using (boolTrue?)

record Beta : Set where
  constructor beta
  field alpha negative : Float

clamp : Float → Float
clamp x with x <ᵇ 0.0
... | true = 0.0
... | false with 1.0 <ᵇ x
...   | true = 1.0
...   | false = x

mean : Beta → Float
mean b with 0.0 <ᵇ (Beta.alpha b + Beta.negative b)
... | true = clamp (Beta.alpha b ÷ (Beta.alpha b + Beta.negative b))
... | false = 0.5

confidence : Beta → Float
confidence b = clamp (((Beta.alpha b + Beta.negative b) - 2.0) ÷ (200.0 - 2.0))

unitInterval : Float → Bool
unitInterval value = (0.0 ≤ᵇ value) ∧ (value ≤ᵇ 1.0)

-- These are application admission rules over supplied Float operations.
-- Zero evidence is allowed; negative/nonfinite counts and an overflowing
-- total are not made valid by a clamped mean or confidence.
record ValidCounts (value : Beta) : Set where
  field
    finiteAlpha : Scores.finite (Beta.alpha value) ≡ true
    finiteBeta : Scores.finite (Beta.negative value) ≡ true
    finiteTotal : Scores.finite (Beta.alpha value + Beta.negative value) ≡ true
    nonnegativeAlpha : (0.0 ≤ᵇ Beta.alpha value) ≡ true
    nonnegativeBeta : (0.0 ≤ᵇ Beta.negative value) ≡ true
    validMean : unitInterval (mean value) ≡ true
    validConfidence : unitInterval (confidence value) ≡ true

validCounts? : ∀ value → Dec (ValidCounts value)
validCounts? value with boolTrue? (Scores.finite (Beta.alpha value)) ×-dec
  (boolTrue? (Scores.finite (Beta.negative value)) ×-dec
  (boolTrue? (Scores.finite (Beta.alpha value + Beta.negative value)) ×-dec
  (boolTrue? (0.0 ≤ᵇ Beta.alpha value) ×-dec
  (boolTrue? (0.0 ≤ᵇ Beta.negative value) ×-dec
  (boolTrue? (unitInterval (mean value)) ×-dec boolTrue? (unitInterval (confidence value)))))))
... | yes (a , b , total , nonnegativeA , nonnegativeB , shownMean , shownConfidence) = yes
  record { finiteAlpha = a ; finiteBeta = b ; finiteTotal = total
         ; nonnegativeAlpha = nonnegativeA ; nonnegativeBeta = nonnegativeB
         ; validMean = shownMean ; validConfidence = shownConfidence }
... | no invalid = no (λ proof → invalid
  (ValidCounts.finiteAlpha proof , ValidCounts.finiteBeta proof , ValidCounts.finiteTotal proof ,
   ValidCounts.nonnegativeAlpha proof , ValidCounts.nonnegativeBeta proof ,
   ValidCounts.validMean proof , ValidCounts.validConfidence proof))

validCounts : Beta → Bool
validCounts value = does (validCounts? value)

validCountsSound : ∀ value → validCounts value ≡ true → ValidCounts value
validCountsSound value = decisionSound (validCounts? value)
  where
  decisionSound : ∀ {A : Set} (decision : Dec A) → does decision ≡ true → A
  decisionSound (yes valid) observed = valid
  decisionSound (no invalid) ()

rejectedDecision : ∀ {A : Set} (decision : Dec A) → (A → ⊥) → does decision ≡ false
rejectedDecision (yes valid) invalid = ⊥-elim (invalid valid)
rejectedDecision (no invalid) rejected = refl

incompatible : ∀ {b} → b ≡ false → b ≡ true → ⊥
incompatible negative positive with trans (sym negative) positive
... | ()

nonfiniteAlphaRefused : ∀ value → Scores.finite (Beta.alpha value) ≡ false → validCounts value ≡ false
nonfiniteAlphaRefused value invalid = rejectedDecision (validCounts? value)
  (λ valid → incompatible invalid (ValidCounts.finiteAlpha valid))

nonfiniteBetaRefused : ∀ value → Scores.finite (Beta.negative value) ≡ false → validCounts value ≡ false
nonfiniteBetaRefused value invalid = rejectedDecision (validCounts? value)
  (λ valid → incompatible invalid (ValidCounts.finiteBeta valid))

overflowingTotalRefused : ∀ value → Scores.finite (Beta.alpha value + Beta.negative value) ≡ false → validCounts value ≡ false
overflowingTotalRefused value invalid = rejectedDecision (validCounts? value)
  (λ valid → incompatible invalid (ValidCounts.finiteTotal valid))

negativeAlphaRefused : ∀ value → (0.0 ≤ᵇ Beta.alpha value) ≡ false → validCounts value ≡ false
negativeAlphaRefused value invalid = rejectedDecision (validCounts? value)
  (λ valid → incompatible invalid (ValidCounts.nonnegativeAlpha valid))

negativeBetaRefused : ∀ value → (0.0 ≤ᵇ Beta.negative value) ≡ false → validCounts value ≡ false
negativeBetaRefused value invalid = rejectedDecision (validCounts? value)
  (λ valid → incompatible invalid (ValidCounts.nonnegativeBeta valid))

-- This includes empty evidence. It states the application's neutral branch
-- for arbitrary counts, without proving the external Float implementation.
nonpositiveTotalIsNeutral : ∀ value → (0.0 <ᵇ (Beta.alpha value + Beta.negative value)) ≡ false → mean value ≡ 0.5
nonpositiveTotalIsNeutral value nonpositive rewrite nonpositive = refl

prior : Float → Float → Beta
prior probability certainty = beta (probability * strength) ((1.0 - probability) * strength)
  where strength = 2.0 + certainty * (200.0 - 2.0)

maximum : Float → Float → Float
maximum a b with isNaN a | isNaN b
... | true | _ = b
... | false | true = a
... | false | false with a <ᵇ b
...   | true = b
...   | false = a

record Node : Set where
  constructor node
  field identity : ℕ; fixed original : Beta

record Edge : Set where
  constructor edge
  field source target : ℕ; relation : Review.Relation; weight : Float

State = List (ℕ × Beta)
External = List (ℕ × Float)
Seed = Maybe (ℕ × Float)

validState : State → Bool
validState [] = true
validState ((_ , value) ∷ rest) = validCounts value ∧ validState rest

andLeft : ∀ a b → a ∧ b ≡ true → a ≡ true
andLeft false b ()
andLeft true b observed = refl

andRight : ∀ a b → a ∧ b ≡ true → b ≡ true
andRight false b ()
andRight true b observed = observed

ValidState : State → Set
ValidState = All (λ { (_ , value) → ValidCounts value })

validStateSound : ∀ values → validState values ≡ true → ValidState values
validStateSound [] observed = []
validStateSound ((_ , value) ∷ rest) observed =
  validCountsSound value (andLeft (validCounts value) (validState rest) observed) ∷
  validStateSound rest (andRight (validCounts value) (validState rest) observed)

validNodes : List Node → Bool
validNodes [] = true
validNodes (value ∷ rest) = validCounts (Node.fixed value) ∧
  validCounts (Node.original value) ∧ validNodes rest

validEdges : List Edge → Bool
validEdges [] = true
validEdges (value ∷ rest) = unitInterval (Edge.weight value) ∧ validEdges rest

referenced : ℕ → List Edge → Bool
referenced id [] = false
referenced id (edgeRow ∷ rest) with id ≟ Edge.source edgeRow
... | yes same = true
... | no different = referenced id rest

-- An unrelated row in another project is not an inference input merely
-- because it is present in the supplied lookup table.
validExternal : List Edge → External → Bool
validExternal edges [] = true
validExternal edges ((id , value) ∷ rest) with referenced id edges
... | false = validExternal edges rest
... | true = unitInterval value ∧ validExternal edges rest

validSeed : Seed → Bool
validSeed nothing = true
validSeed (just (_ , value)) = unitInterval value

lookup : ∀ {A : Set} → ℕ → List (ℕ × A) → Maybe A
lookup id [] = nothing
lookup id ((key , value) ∷ rest) with id ≟ key
... | yes same = just value
... | no different = lookup id rest

write : ℕ → Beta → State → State
write id value [] = []
write id value ((key , old) ∷ rest) with id ≟ key
... | yes same = (key , value) ∷ rest
... | no different = (key , old) ∷ write id value rest

unclamped : ℕ → State → External → Maybe Float
unclamped id state external with lookup id state
... | just b = just (mean b)
... | nothing = lookup id external

parent : Seed → ℕ → State → External → Maybe Float
parent nothing id state external = unclamped id state external
parent (just (seed , value)) id state external with id ≟ seed
... | yes same = just value
... | no different = unclamped id state external

contribute : Review.Relation → Float → Beta → Beta
contribute Review.supports delta b = beta (Beta.alpha b + delta) (Beta.negative b)
contribute Review.causes delta b = beta (Beta.alpha b + delta) (Beta.negative b)
contribute Review.defeats delta b = beta (Beta.alpha b) (Beta.negative b + delta)
contribute Review.contradicts delta b = b

contributesEvidence : Review.Relation → Bool
contributesEvidence Review.supports = true
contributesEvidence Review.causes = true
contributesEvidence Review.defeats = true
contributesEvidence Review.contradicts = false

incoming : Seed → ℕ → State → External → List Edge → Beta → Beta
incoming seed target state external [] b = b
incoming seed target state external (e ∷ es) b with target ≟ Edge.target e
... | no different = incoming seed target state external es b
... | yes same with contributesEvidence (Edge.relation e)
...   | false = incoming seed target state external es b
...   | true with parent seed (Edge.source e) state external
...     | nothing = incoming seed target state external es b
...     | just probability = incoming seed target state external es
  (contribute (Edge.relation e) ((Edge.weight e * probability) * 4.0) b)

-- This goal describes the final values, independently of traversal or passes.
-- A missing or stale descendant cannot satisfy it.
PosteriorGoal : Seed → External → List Edge → List Node → State → Set
PosteriorGoal seed external edges nodes final = All (λ n →
  lookup (Node.identity n) final ≡ just
    (incoming seed (Node.identity n) final external edges (Node.fixed n))) nodes

lookupOtherWrite : ∀ identity written value state → identity ≢ written →
  lookup identity (write written value state) ≡ lookup identity state
lookupOtherWrite identity written value [] different = refl
lookupOtherWrite identity written value ((key , old) ∷ rest) different
  with written ≟ key in writtenEq | identity ≟ key in identityEq
... | yes same | yes other = ⊥-elim (different (trans other (sym same)))
... | yes same | no other rewrite identityEq = refl
... | no same | yes other rewrite identityEq = refl
... | no same | no other rewrite identityEq = lookupOtherWrite identity written value rest different

lookupWritten : ∀ identity value state old → lookup identity state ≡ just old →
  lookup identity (write identity value state) ≡ just value
lookupWritten identity value [] old ()
lookupWritten identity value ((key , before) ∷ rest) old present with identity ≟ key in keyEq
... | yes same rewrite keyEq = refl
... | no different rewrite keyEq = lookupWritten identity value rest old present

parentOtherWrite : ∀ seed identity written value state external → identity ≢ written →
  parent seed identity (write written value state) external ≡ parent seed identity state external
parentOtherWrite nothing identity written value state external different
  rewrite lookupOtherWrite identity written value state different = refl
parentOtherWrite (just (fixed , probability)) identity written value state external different
  with identity ≟ fixed
... | yes same = refl
... | no other rewrite lookupOtherWrite identity written value state different = refl

unused : ℕ → ℕ → Edge → Bool
unused target written e with target ≟ Edge.target e
... | no other = true
... | yes same with contributesEvidence (Edge.relation e)
...   | false = true
...   | true = not (does (Edge.source e ≟ written))

Unused : ℕ → ℕ → List Edge → Set
Unused target written edges = All (λ e → unused target written e ≡ true) edges

differentSound : ∀ first second → not (does (first ≟ second)) ≡ true → first ≢ second
differentSound zero zero ()
differentSound zero (suc second) observed ()
differentSound (suc first) zero observed ()
differentSound (suc first) (suc .first) observed refl = differentSound first first observed refl

incomingOtherWrite : ∀ seed target written value state external edges base →
  Unused target written edges →
  incoming seed target (write written value state) external edges base ≡
    incoming seed target state external edges base
incomingOtherWrite seed target written value state external [] base [] = refl
incomingOtherWrite seed target written value state external (e ∷ es) base (proof ∷ rest)
  with target ≟ Edge.target e
... | no other = incomingOtherWrite seed target written value state external es base rest
... | yes same with contributesEvidence (Edge.relation e)
...   | false = incomingOtherWrite seed target written value state external es base rest
...   | true rewrite parentOtherWrite seed (Edge.source e) written value state external
      (differentSound (Edge.source e) written proof)
      with parent seed (Edge.source e) state external
...     | nothing = incomingOtherWrite seed target written value state external es base rest
...     | just probability = incomingOtherWrite seed target written value state external es
      (contribute (Edge.relation e) ((Edge.weight e * probability) * 4.0) base) rest

-- All graph conditions below concern identities and edges. No caller can
-- provide the desired posterior as an ordering certificate.
allDec : ∀ {A : Set} {P : A → Set} → (∀ value → Dec (P value)) →
  (values : List A) → Dec (All P values)
allDec decide [] = yes []
allDec decide (value ∷ rest) with decide value | allDec decide rest
... | yes proof | yes proofs = yes (proof ∷ proofs)
... | no invalid | _ = no (λ { (proof ∷ _) → invalid proof })
... | yes _ | no invalid = no (λ { (_ ∷ proofs) → invalid proofs })

unused? : ∀ target written edges → Dec (Unused target written edges)
unused? target written = allDec (λ e → boolTrue? (unused target written e))

Ready : ℕ → List Node → List Edge → Set
Ready target nodes edges = All (λ n → Unused target (Node.identity n) edges) nodes

Distinct : ℕ → List Node → Set
Distinct identity nodes = All (λ n → identity ≢ Node.identity n) nodes

distinct? : ∀ identity nodes → Dec (Distinct identity nodes)
distinct? identity = allDec different
  where
  different : ∀ n → Dec (identity ≢ Node.identity n)
  different n with identity ≟ Node.identity n
  ... | yes same = no (λ denied → denied same)
  ... | no denied = yes denied

data Placement (selected : Node) : List Node → List Node → Set where
  here : ∀ rest → Placement selected (selected ∷ rest) rest
  later : ∀ first before after → Placement selected before after →
    Placement selected (first ∷ before) (first ∷ after)

selectedAll : ∀ {P : Node → Set} {selected before after} →
  Placement selected before after → All P before → P selected × All P after
selectedAll (here _) (proof ∷ proofs) = proof , proofs
selectedAll (later first before after placement) (proof ∷ proofs)
  with selectedAll placement proofs
... | selected , remaining = selected , proof ∷ remaining

restoreAll : ∀ {P : Node → Set} {selected before after} →
  Placement selected before after → P selected → All P after → All P before
restoreAll (here _) proof proofs = proof ∷ proofs
restoreAll (later first before after placement) proof (firstProof ∷ proofs) =
  firstProof ∷ restoreAll placement proof proofs

data DependencyPlan (edges : List Edge) : List Node → List Node → Set where
  emptyPlan : DependencyPlan edges [] []
  selectedPlan : ∀ selected before remaining ordered →
    Placement selected before remaining → Ready (Node.identity selected) before edges →
    Distinct (Node.identity selected) remaining → DependencyPlan edges remaining ordered →
    DependencyPlan edges before (selected ∷ ordered)

planAll : ∀ {P : Node → Set} {edges before ordered} →
  DependencyPlan edges before ordered → All P before → All P ordered
planAll emptyPlan [] = []
planAll (selectedPlan selected before remaining ordered placement ready distinct plan) proofs
  with selectedAll placement proofs
... | first , rest = first ∷ planAll plan rest

planRestoresAll : ∀ {P : Node → Set} {edges before ordered} →
  DependencyPlan edges before ordered → All P ordered → All P before
planRestoresAll emptyPlan [] = []
planRestoresAll (selectedPlan selected before remaining ordered placement ready distinct plan)
  (first ∷ rest) = restoreAll placement first (planRestoresAll plan rest)

Choice : List Edge → List Node → List Node → Set
Choice edges pending candidates = Σ Node (λ selected → Σ (List Node) (λ remaining →
  Placement selected candidates remaining × Ready (Node.identity selected) pending edges))

choose : ∀ edges pending candidates → Maybe (Choice edges pending candidates)
choose edges pending [] = nothing
choose edges pending (n ∷ ns) with allDec (λ other → unused? (Node.identity n) (Node.identity other) edges) pending
... | yes ready = just (n , ns , here ns , ready)
... | no blocked with choose edges pending ns
...   | nothing = nothing
...   | just (selected , remaining , placement , ready) =
  just (selected , n ∷ remaining , later n ns remaining placement , ready)

-- The measure is the actual number of nodes, not an application quota. Each
-- successful selection removes one input node, and no node can be skipped.
dependencyOrder : ∀ edges → ℕ → (pending : List Node) →
  Maybe (Σ (List Node) (DependencyPlan edges pending))
dependencyOrder edges fuel [] = just ([] , emptyPlan)
dependencyOrder edges zero (_ ∷ _) = nothing
dependencyOrder edges (suc fuel) pending@(_ ∷ _) with choose edges pending pending
... | nothing = nothing
... | just (selected , remaining , placement , ready) with distinct? (Node.identity selected) remaining
...   | no duplicate = nothing
...   | yes distinct with dependencyOrder edges fuel remaining
...     | nothing = nothing
...     | just (ordered , plan) = just (selected ∷ ordered ,
  selectedPlan selected pending remaining ordered placement ready distinct plan)

data ReadyOrder (edges : List Edge) : List Node → Set where
  emptyOrder : ReadyOrder edges []
  firstReady : ∀ first rest → Unused (Node.identity first) (Node.identity first) edges →
    Ready (Node.identity first) rest edges → Distinct (Node.identity first) rest →
    ReadyOrder edges rest → ReadyOrder edges (first ∷ rest)

planReady : ∀ {edges before ordered} → DependencyPlan edges before ordered → ReadyOrder edges ordered
planReady emptyPlan = emptyOrder
planReady (selectedPlan selected before remaining ordered placement ready distinct plan)
  with selectedAll placement ready
... | self , rest = firstReady selected ordered self (planAll plan rest)
  (planAll plan distinct) (planReady plan)

data PlacementPair (first second : Node) (withoutFirst withoutSecond : List Node) : Set where
  samePlace : first ≡ second → withoutFirst ≡ withoutSecond →
    PlacementPair first second withoutFirst withoutSecond
  separatePlaces : ∀ remaining → Placement second withoutFirst remaining →
    Placement first withoutSecond remaining → PlacementPair first second withoutFirst withoutSecond

comparePlacements : ∀ {first second before withoutFirst withoutSecond} →
  Placement first before withoutFirst → Placement second before withoutSecond →
  PlacementPair first second withoutFirst withoutSecond
comparePlacements (here rest) (here .rest) = samePlace refl refl
comparePlacements (here rest) (later ._ .rest after placement) =
  separatePlaces after placement (here after)
comparePlacements (later ._ before after placement) (here .before) =
  separatePlaces after (here after) placement
comparePlacements (later first before left placement) (later .first .before right other)
  with comparePlacements placement other
... | samePlace refl refl = samePlace refl refl
... | separatePlaces remaining secondLeft firstRight = separatePlaces (first ∷ remaining)
  (later first left remaining secondLeft) (later first right remaining firstRight)

-- Removing a vertex from an acyclic graph leaves an acyclic graph, whichever
-- ready vertex the executable selector happens to choose first.
removeFromPlan : ∀ {selected edges before remaining ordered} →
  Placement selected before remaining → DependencyPlan edges before ordered →
  Σ (List Node) (DependencyPlan edges remaining)
removeFromPlan () emptyPlan
removeFromPlan selectedPlacement
  (selectedPlan first before after ordered firstPlacement ready distinct plan)
  with comparePlacements firstPlacement selectedPlacement
... | samePlace refl refl = ordered , plan
... | separatePlaces remaining selectedAfter firstRemaining
  with removeFromPlan selectedAfter plan
...   | rest , restPlan = first ∷ rest , selectedPlan first _ remaining rest firstRemaining
  (proj₂ (selectedAll selectedPlacement ready))
  (proj₂ (selectedAll selectedAfter distinct)) restPlan

data Unique : List Node → Set where
  emptyUnique : Unique []
  firstUnique : ∀ first rest → Distinct (Node.identity first) rest → Unique rest → Unique (first ∷ rest)

restoreUnique : ∀ {selected before after} → Placement selected before after →
  Distinct (Node.identity selected) after → Unique after → Unique before
restoreUnique (here rest) distinct unique = firstUnique _ rest distinct unique
restoreUnique (later first before after placement) (different ∷ distinct)
  (firstUnique .first .after firstDistinct unique) = firstUnique first before
    (restoreAll placement (λ same → different (sym same)) firstDistinct)
    (restoreUnique placement distinct unique)

planUnique : ∀ {edges before ordered} → DependencyPlan edges before ordered → Unique before
planUnique emptyPlan = emptyUnique
planUnique (selectedPlan selected before remaining ordered placement ready distinct plan) =
  restoreUnique placement distinct (planUnique plan)

selectionDistinct : ∀ {selected before after} → Placement selected before after →
  Unique before → Distinct (Node.identity selected) after
selectionDistinct (here rest) (firstUnique _ .rest distinct unique) = distinct
selectionDistinct (later first before after placement) (firstUnique .first .before distinct unique)
  with selectedAll placement distinct
... | firstDifferent , rest = (λ same → firstDifferent (sym same)) ∷ selectionDistinct placement unique

chooseFindsReady : ∀ edges pending candidates selected remaining →
  Placement selected candidates remaining → Ready (Node.identity selected) pending edges →
  Σ (Choice edges pending candidates) (λ choice → choose edges pending candidates ≡ just choice)
chooseFindsReady edges pending .(selected ∷ remaining) selected remaining (here .remaining) ready
  with allDec (λ other → unused? (Node.identity selected) (Node.identity other) edges) pending
... | yes actual = (selected , remaining , here remaining , actual) , refl
... | no invalid = ⊥-elim (invalid ready)
chooseFindsReady edges pending .(first ∷ before) selected .(first ∷ after)
  (later first before after placement) ready
  with allDec (λ other → unused? (Node.identity first) (Node.identity other) edges) pending
... | yes actual = (first , before , here before , actual) , refl
... | no blocked with chooseFindsReady edges pending before selected after placement ready
...   | (found , remaining , foundPlacement , foundReady) , observed rewrite observed =
  (found , first ∷ remaining , later first before remaining foundPlacement , foundReady) , refl

placementLength : ∀ {selected before after} → Placement selected before after → length before ≡ suc (length after)
placementLength (here _) = refl
placementLength (later first before after placement) = cong suc (placementLength placement)

remainingEnough : ∀ {selected before after} fuel → Placement selected before after →
  length before ≤ suc fuel → length after ≤ fuel
remainingEnough fuel placement enough = strip
  (subst (λ size → size ≤ suc fuel) (placementLength placement) enough)
  where
  strip : ∀ {first second} → suc first ≤ suc second → first ≤ second
  strip (s≤s proof) = proof

dependencyOrderProgress : ∀ fuel edges pending ordered → DependencyPlan edges pending ordered →
  length pending ≤ fuel → Σ (List Node) (λ resolved → Σ (DependencyPlan edges pending resolved)
    (λ plan → dependencyOrder edges fuel pending ≡ just (resolved , plan)))
dependencyOrderProgress fuel edges [] .[] emptyPlan enough = [] , emptyPlan , refl
dependencyOrderProgress zero edges (_ ∷ _) ordered plan ()
dependencyOrderProgress (suc fuel) edges pending@(_ ∷ _) .(first ∷ ordered)
  original@(selectedPlan first .pending after ordered placement ready distinct plan) enough
  with chooseFindsReady edges pending pending first after placement ready
... | (selected , remaining , selectedPlacement , selectedReady) , observed rewrite observed
  with distinct? (Node.identity selected) remaining
...   | no invalid = ⊥-elim (invalid (selectionDistinct selectedPlacement (planUnique original)))
...   | yes selectedDistinct with removeFromPlan selectedPlacement original
...     | rest , restPlan with dependencyOrderProgress fuel edges remaining rest restPlan
    (remainingEnough fuel selectedPlacement enough)
...       | resolved , resolvedPlan , completed rewrite completed =
  selected ∷ resolved , selectedPlan selected pending remaining resolved selectedPlacement
    selectedReady selectedDistinct resolvedPlan , refl

calculate : Seed → External → List Edge → List Node → State → State
calculate seed external edges [] state = state
calculate seed external edges (n ∷ ns) state = calculate seed external edges ns
  (write (Node.identity n) (incoming seed (Node.identity n) state external edges (Node.fixed n)) state)

calculationPreservesLookup : ∀ seed external edges nodes state identity → Distinct identity nodes →
  lookup identity (calculate seed external edges nodes state) ≡ lookup identity state
calculationPreservesLookup seed external edges [] state identity [] = refl
calculationPreservesLookup seed external edges (n ∷ ns) state identity (different ∷ rest) =
  trans (calculationPreservesLookup seed external edges ns updated identity rest)
    (lookupOtherWrite identity (Node.identity n) value state different)
  where
  value = incoming seed (Node.identity n) state external edges (Node.fixed n)
  updated = write (Node.identity n) value state

calculationPreservesIncoming : ∀ seed external edges nodes state identity base → Ready identity nodes edges →
  incoming seed identity (calculate seed external edges nodes state) external edges base ≡
    incoming seed identity state external edges base
calculationPreservesIncoming seed external edges [] state identity base [] = refl
calculationPreservesIncoming seed external edges (n ∷ ns) state identity base (unused ∷ rest) =
  trans (calculationPreservesIncoming seed external edges ns updated identity base rest)
    (incomingOtherWrite seed identity (Node.identity n) value state external edges base unused)
  where
  value = incoming seed (Node.identity n) state external edges (Node.fixed n)
  updated = write (Node.identity n) value state

Covers : List Node → State → Set
Covers nodes state = All (λ n → Σ Beta (λ value → lookup (Node.identity n) state ≡ just value)) nodes

coversAfterWrite : ∀ nodes state written value → Distinct written nodes → Covers nodes state →
  Covers nodes (write written value state)
coversAfterWrite [] state written value [] [] = []
coversAfterWrite (n ∷ ns) state written value (different ∷ rest) ((old , present) ∷ remainingCovers) =
  (old , trans (lookupOtherWrite (Node.identity n) written value state (λ same → different (sym same))) present) ∷
  coversAfterWrite ns state written value rest remainingCovers

calculationMeetsGoal : ∀ seed external edges nodes initial → Covers nodes initial → ReadyOrder edges nodes →
  PosteriorGoal seed external edges nodes (calculate seed external edges nodes initial)
calculationMeetsGoal seed external edges [] initial [] emptyOrder = []
calculationMeetsGoal seed external edges (n ∷ ns) initial ((old , present) ∷ remainingCovers)
  (firstReady .n .ns self unused distinct ready) = first ∷ rest
  where
  value = incoming seed (Node.identity n) initial external edges (Node.fixed n)
  updated = write (Node.identity n) value initial
  final = calculate seed external edges ns updated
  incomingStable = calculationPreservesIncoming seed external edges (n ∷ ns) initial
    (Node.identity n) (Node.fixed n) (self ∷ unused)
  first : lookup (Node.identity n) final ≡ just
    (incoming seed (Node.identity n) final external edges (Node.fixed n))
  first = trans (calculationPreservesLookup seed external edges ns updated (Node.identity n) distinct)
    (trans (lookupWritten (Node.identity n) value initial old present) (cong just (sym incomingStable)))
  rest = calculationMeetsGoal seed external edges ns updated
    (coversAfterWrite ns initial (Node.identity n) value distinct remainingCovers) ready

-- Every plan produced by dependencyOrder retains ALL original targets, and
-- its complete result satisfies the independent per-node posterior equations.
dependencyCalculationComplete : ∀ seed external edges before ordered initial →
  (plan : DependencyPlan edges before ordered) → Covers before initial →
  PosteriorGoal seed external edges before (calculate seed external edges ordered initial)
dependencyCalculationComplete seed external edges before ordered initial plan present =
  planRestoresAll plan (calculationMeetsGoal seed external edges ordered initial
    (planAll plan present) (planReady plan))

isSeed : Seed → ℕ → Bool
isSeed nothing id = false
isSeed (just (seed , value)) id with id ≟ seed
... | yes same = true
... | no different = false

insert : Node → List Node → List Node
insert n [] = n ∷ []
insert n (m ∷ ms) with Node.identity n ≤? Node.identity m
... | yes before = n ∷ m ∷ ms
... | no after = m ∷ insert n ms

order : Seed → List Node → List Node
order seed [] = []
order seed (n ∷ ns) with isSeed seed (Node.identity n)
... | true = order seed ns
... | false = insert n (order seed ns)

insertAll : ∀ {P : Node → Set} n nodes → P n → All P nodes → All P (insert n nodes)
insertAll n [] proof [] = proof ∷ []
insertAll n (first ∷ rest) proof (firstProof ∷ proofs) with Node.identity n ≤? Node.identity first
... | yes before = proof ∷ firstProof ∷ proofs
... | no after = firstProof ∷ insertAll n rest proof proofs

orderAll : ∀ {P : Node → Set} seed nodes → All P nodes → All P (order seed nodes)
orderAll seed [] [] = []
orderAll seed (n ∷ ns) (proof ∷ proofs) with isSeed seed (Node.identity n)
... | true = orderAll seed ns proofs
... | false = insertAll n (order seed ns) proof (orderAll seed ns proofs)

firstPresent : ∀ identity (value : Beta) (state : State) → lookup identity ((identity , value) ∷ state) ≡ just value
firstPresent identity value state with identity ≟ identity
... | yes same = refl
... | no different = ⊥-elim (different refl)

nodeUnderRow : ∀ identity value n state →
  Σ Beta (λ old → lookup (Node.identity n) state ≡ just old) →
  Σ Beta (λ old → lookup (Node.identity n) ((identity , value) ∷ state) ≡ just old)
nodeUnderRow identity value n state (old , present) with Node.identity n ≟ identity
... | yes same = value , refl
... | no different = old , present

coversUnderRow : ∀ identity value nodes state → Covers nodes state → Covers nodes ((identity , value) ∷ state)
coversUnderRow identity value [] state [] = []
coversUnderRow identity value (n ∷ ns) state (present ∷ proofs) =
  nodeUnderRow identity value n state present ∷ coversUnderRow identity value ns state proofs

initial : List Node → State
initial = map (λ n → Node.identity n , Node.fixed n)

initialCoversEveryNode : ∀ nodes → Covers nodes (initial nodes)
initialCoversEveryNode [] = []
initialCoversEveryNode (n ∷ ns) =
  (Node.fixed n , firstPresent (Node.identity n) (Node.fixed n) (initial ns)) ∷
  coversUnderRow (Node.identity n) (Node.fixed n) ns (initial ns) (initialCoversEveryNode ns)

record Sweep : Set where
  constructor sweepResult
  field state : State; delta : Float; numericFailure : Bool

sweep : Seed → External → List Edge → List Node → State → Float → Sweep
sweep seed external edges [] state delta = sweepResult state delta false
sweep seed external edges (n ∷ ns) state delta with lookup (Node.identity n) state
... | nothing = sweep seed external edges ns state delta
... | just old with validCounts updated
  where updated = incoming seed (Node.identity n) state external edges (Node.fixed n)
...   | false = sweepResult state delta true
...   | true = sweep seed external edges ns (write (Node.identity n) updated state)
  (maximum delta (Scores.absolute (mean updated - mean old)))
  where updated = incoming seed (Node.identity n) state external edges (Node.fixed n)

record Outcome : Set where
  constructor outcome
  field state : State; converged numericFailure : Bool

iterate : ℕ → Seed → External → List Edge → List Node → State → Outcome
iterate zero seed external edges nodes state = outcome state false false
iterate (suc fuel) seed external edges nodes state
  with sweep seed external edges nodes state 0.0
... | sweepResult after delta true = outcome after false true
... | sweepResult after delta false with delta <ᵇ 0.000000001
...   | true = outcome after true false
...   | false = iterate fuel seed external edges nodes after

changed : Beta → Beta → Bool
changed old new =
  (Beta.alpha old <ᵇ Beta.alpha new) ∨ (Beta.alpha new <ᵇ Beta.alpha old) ∨
  (Beta.negative old <ᵇ Beta.negative new) ∨ (Beta.negative new <ᵇ Beta.negative old)

updates : List Node → State → State
updates [] state = []
updates (n ∷ ns) state with lookup (Node.identity n) state
... | nothing = updates ns state
... | just b with changed (Node.original n) b
...   | false = updates ns state
...   | true = (Node.identity n , b) ∷ updates ns state

record Result : Set where
  constructor result
  field writes : State; iterationLimitReached numericFailure : Bool

finish : List Node → Outcome → Result
finish nodes (outcome final converged true) = result [] false true
finish nodes (outcome final converged false) with validState final
... | false = result [] false true
... | true = result (updates nodes final) (not converged) false

calculation : Seed → External → List Edge → List Node → State → Outcome
calculation seed external edges ordered initial with dependencyOrder edges (length ordered) ordered
... | nothing = iterate 50 seed external edges ordered initial
... | just (resolved , plan) = outcome (calculate seed external edges resolved initial) true false

-- The selection is the one used by the actual application calculation.
-- Its certificate is computed from the graph, not supplied by a request.
acyclicApplicationCalculationComplete : ∀ seed external edges nodes resolved plan →
  dependencyOrder edges (length (order seed nodes)) (order seed nodes) ≡ just (resolved , plan) →
  PosteriorGoal seed external edges (order seed nodes)
    (Outcome.state (calculation seed external edges (order seed nodes) (initial nodes)))
acyclicApplicationCalculationComplete seed external edges nodes resolved plan selected rewrite selected =
  dependencyCalculationComplete seed external edges (order seed nodes) resolved (initial nodes) plan
    (orderAll seed nodes (initialCoversEveryNode nodes))

-- Acyclic means a dependency ordering exists, independently of which order
-- the selector chooses. This theorem includes progress: such an input cannot
-- fall through to the old cyclic pass allowance, at any graph depth.
acyclicApplicationAlwaysCompletes : ∀ seed external edges nodes witness →
  DependencyPlan edges (order seed nodes) witness →
  Σ (List Node) (λ resolved → Σ (DependencyPlan edges (order seed nodes) resolved) (λ plan →
    dependencyOrder edges (length (order seed nodes)) (order seed nodes) ≡ just (resolved , plan) ×
    PosteriorGoal seed external edges (order seed nodes)
      (Outcome.state (calculation seed external edges (order seed nodes) (initial nodes)))))
acyclicApplicationAlwaysCompletes seed external edges nodes witness proof
  with dependencyOrderProgress (length (order seed nodes)) edges (order seed nodes) witness proof ≤-refl
... | resolved , plan , selected = resolved , plan , selected ,
  acyclicApplicationCalculationComplete seed external edges nodes resolved plan selected

run : Seed → External → List Edge → List Node → Result
run seed external edges nodes with validSeed seed ∧ validExternal edges external ∧ validEdges edges ∧ validNodes nodes
... | false = result [] false true
... | true = finish ordered (calculation seed external edges ordered (initial nodes))
  where
  ordered = order seed nodes

contradictionInert : ∀ delta b → contribute Review.contradicts delta b ≡ b
contradictionInert delta b = refl

exhaustionReturnsCurrent : ∀ seed external edges nodes state →
  iterate zero seed external edges nodes state ≡ outcome state false false
exhaustionReturnsCurrent seed external edges nodes state = refl
