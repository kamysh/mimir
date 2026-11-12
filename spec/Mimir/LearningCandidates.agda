{-# OPTIONS --safe #-}
module Mimir.LearningCandidates where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Mimir.UUIDGroups using (_≟UUID_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Mimir.Text
open import Mimir.SourceSchema using (NamedText; checkNamed)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.LearningSchema using (Target; existing; candidate)
open import Mimir.Validation
import Mimir.Collections as Collections

data Memory : Set where fact experiential working : Memory
data Candidate : Set where
  belief : (key content : Text) → Memory → Candidate
  patternCandidate : (key situation approach : Text) → Candidate

memoryEqual : (x y : Memory) → Dec (x ≡ y)
memoryEqual fact fact = yes refl
memoryEqual fact experiential = no (λ ())
memoryEqual fact working = no (λ ())
memoryEqual experiential fact = no (λ ())
memoryEqual experiential experiential = yes refl
memoryEqual experiential working = no (λ ())
memoryEqual working fact = no (λ ())
memoryEqual working experiential = no (λ ())
memoryEqual working working = yes refl

candidateEqual : (x y : Candidate) → Dec (x ≡ y)
candidateEqual (belief name content memory) (belief other body kind)
  with name ≟Text other | content ≟Text body | memoryEqual memory kind
... | yes refl | yes refl | yes refl = yes refl
... | no different | _ | _ = no (λ { refl → different refl })
... | _ | no different | _ = no (λ { refl → different refl })
... | _ | _ | no different = no (λ { refl → different refl })
candidateEqual (patternCandidate name situation approach) (patternCandidate other context action)
  with name ≟Text other | situation ≟Text context | approach ≟Text action
... | yes refl | yes refl | yes refl = yes refl
... | no different | _ | _ = no (λ { refl → different refl })
... | _ | no different | _ = no (λ { refl → different refl })
... | _ | _ | no different = no (λ { refl → different refl })
candidateEqual (belief _ _ _) (patternCandidate _ _ _) = no (λ ())
candidateEqual (patternCandidate _ _ _) (belief _ _ _) = no (λ ())

candidateKey : Candidate → Text
candidateKey (belief name content memory) = name
candidateKey (patternCandidate name situation approach) = name

Trimmed : Text → Set
Trimmed text = NamedText text × text ≡ trim text

checkTrimmed : ∀ text → Checked (Trimmed text)
checkTrimmed text = combine (checkNamed text)
  (check (fault [] malformedInput "reference must be trimmed") (text ≟Text trim text))

Persistent : Memory → Set
Persistent fact = ⊤
Persistent experiential = ⊤
Persistent working = ⊥

checkPersistent : ∀ memory → Checked (Persistent memory)
checkPersistent fact = accepted tt
checkPersistent experiential = accepted tt
checkPersistent working = rejected
  (fault [] unsupportedCombination "working memory cannot be a review candidate") (λ p → p)

BodyValid : Candidate → Set
BodyValid (belief name content memory) = Nonblank content × Persistent memory
BodyValid (patternCandidate name situation approach) = Nonblank situation × Nonblank approach

checkNonblank : ∀ text → Checked (Nonblank text)
checkNonblank text = check (fault [] emptyText "text must contain a non-whitespace character") (nonblank? text)

checkBody : ∀ c → Checked (BodyValid c)
checkBody (belief name content memory) = combine
  (at (key "content") (checkNonblank content)) (at (key "memory_type") (checkPersistent memory))
checkBody (patternCandidate name situation approach) = combine
  (at (key "situation") (checkNonblank situation)) (at (key "approach") (checkNonblank approach))

Valid : Candidate → Set
Valid c = Trimmed (candidateKey c) × BodyValid c

validate : ∀ c → Checked (Valid c)
validate c = combine (at (key "key") (checkTrimmed (candidateKey c))) (checkBody c)

beliefKeys : List Candidate → List Text
beliefKeys [] = []
beliefKeys (belief name content memory ∷ rest) = name ∷ beliefKeys rest
beliefKeys (patternCandidate name situation approach ∷ rest) = beliefKeys rest

module Keys = Collections.Equality Text _≟Text_

TargetValid : List Candidate → Target → Set
TargetValid candidates (existing id) = ⊤
TargetValid candidates (candidate name) = Keys.Present name (beliefKeys candidates)

validateTarget : ∀ candidates target → Checked (TargetValid candidates target)
validateTarget candidates (existing id) = accepted tt
validateTarget candidates (candidate name) = check
  (fault [] missingReference "candidate belief must be declared in this review")
  (Keys.present? name (beliefKeys candidates))

targetEqual : (x y : Target) → Dec (x ≡ y)
targetEqual (existing x) (existing y) with x ≟UUID y
... | yes refl = yes refl
... | no different = no (λ { refl → different refl })
targetEqual (candidate x) (candidate y) with x ≟Text y
... | yes refl = yes refl
... | no different = no (λ { refl → different refl })
targetEqual (existing _) (candidate _) = no (λ ())
targetEqual (candidate _) (existing _) = no (λ ())

module Targets = Collections.Equality Target targetEqual

-- A pattern declaration cannot satisfy a belief-target reference. This is
-- quantified over all preceding/following review candidates, not an example.
patternAddsNoBeliefTarget : ∀ name situation approach rest target →
  TargetValid (patternCandidate name situation approach ∷ rest) target ≡ TargetValid rest target
patternAddsNoBeliefTarget name situation approach rest (existing id) = refl
patternAddsNoBeliefTarget name situation approach rest (candidate reference) = refl

workingNeverValid : ∀ name content → Valid (belief name content working) → ⊥
workingNeverValid name content (keyProof , contentProof , impossible) = impossible

validNeverRejected : ∀ c → Valid c → reported (validate c) ≡ []
validNeverRejected c = noFalseRejection (validate c)
