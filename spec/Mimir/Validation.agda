{-# OPTIONS --safe #-}
-- Error-bearing decisions. A rejection includes the negation of the contract;
-- accepted values include its proof. Error descriptions remain data, not axioms.
module Mimir.Validation where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; suc)
open import Data.String using (String; toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Mimir.Text using (Text)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Segment : Set where
  fieldKey : Text → Segment
  index : ℕ → Segment

-- Literal conveniences convert only at construction. Stored diagnostics use
-- the same explicit character sequences as the wire model; no primitive
-- String/List inverse law is assumed for serialization proofs.
key : String → Segment
key name = fieldKey (toList name)

data Code : Set where
  emptyText textTooLong tooMany duplicate missingReference wrongActor
    quotationMismatch staleRevision wrongIdentity invalidNumber invalidInterval
    missingEvidence unsupportedCombination malformedInput : Code

record Fault : Set where
  constructor problem
  field
    path : List Segment
    code : Code
    explanation : Text
open Fault public

fault : List Segment → Code → String → Fault
fault path code message = problem path code (toList message)

data Checked (P : Set) : Set where
  accepted : P → Checked P
  rejected : Fault → ¬ P → Checked P

result : ∀ {P} → Checked P → Fault ⊎ P
result (accepted proof) = inj₂ proof
result (rejected failure invalid) = inj₁ failure

check : ∀ {P} → Fault → Dec P → Checked P
check failure (yes proof) = accepted proof
check failure (no refutation) = rejected failure refutation

combine : ∀ {P Q} → Checked P → Checked Q → Checked (P × Q)
combine (rejected failure noP) right = rejected failure (λ pair → noP (proj₁ pair))
combine (accepted p) (rejected failure noQ) = rejected failure (λ pair → noQ (proj₂ pair))
combine (accepted p) (accepted q) = accepted (p , q)

firstFailure : ∀ {P Q} (failure : Fault) (noP : ¬ P) (right : Checked Q) →
  combine (rejected failure noP) right ≡ rejected failure (λ pair → noP (proj₁ pair))
firstFailure failure noP right = refl

-- Successful validation and genuine invalidity cannot coexist.
acceptedCannotBeInvalid : ∀ {P : Set} → P → ¬ P → ⊥
acceptedCannotBeInvalid p noP = noP p

reported : ∀ {P} → Checked P → List Fault
reported (accepted _) = []
reported (rejected failure _) = failure ∷ []

noFalseRejection : ∀ {P} (result : Checked P) → P → reported result ≡ []
noFalseRejection (accepted _) proof = refl
noFalseRejection (rejected failure notValid) proof = ⊥-elim (notValid proof)

allCheckedFrom : ∀ {A : Set} {P : A → Set} → ℕ →
  ((a : A) → Checked (P a)) → (xs : List A) → Checked (All P xs)
allCheckedFrom offset f [] = accepted []
allCheckedFrom offset f (x ∷ xs) with f x
... | rejected failure notP = rejected
  (problem (index offset ∷ path failure) (code failure) (explanation failure))
  (λ { (p ∷ ps) → notP p })
... | accepted p with allCheckedFrom (suc offset) f xs
...   | accepted ps = accepted (p ∷ ps)
...   | rejected failure notAll = rejected failure (λ { (q ∷ qs) → notAll qs })

allChecked : ∀ {A : Set} {P : A → Set} →
  ((a : A) → Checked (P a)) → (xs : List A) → Checked (All P xs)
allChecked = allCheckedFrom 0

prependPath : Segment → Fault → Fault
prependPath segment (problem path code explanation) = problem (segment ∷ path) code explanation

at : ∀ {P} → Segment → Checked P → Checked P
at segment (accepted proof) = accepted proof
at segment (rejected failure refutation) = rejected (prependPath segment failure) refutation

-- The same semantic fault reaches the judge and the durable diagnostic. A
-- backend/transport error is not a validation fault and has its own protocol.
record Feedback : Set where
  constructor feedback
  field model diagnostic : Fault

deliver : Fault → Feedback
deliver failure = feedback failure failure

modelGetsExactFault : ∀ failure → Feedback.model (deliver failure) ≡ failure
modelGetsExactFault failure = refl

diagnosticAgrees : ∀ failure →
  Feedback.model (deliver failure) ≡ Feedback.diagnostic (deliver failure)
diagnosticAgrees failure = refl
