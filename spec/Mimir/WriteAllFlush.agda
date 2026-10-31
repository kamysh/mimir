{-# OPTIONS --safe #-}
-- Observed partial-write and flush receipts. Failure retains the observed
-- prefix and pending suffix; neither means that a remote action was undone.
module Mimir.WriteAllFlush where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; length; take; drop)
open import Data.List.Properties using (++-assoc; ++-identityʳ; take++drop≡id; length-drop)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _≤?_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m∸n≤m)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import Mimir.Text using (Text)
open import Mimir.Bits using (Byte)

data Failure : Set where
  writeZero invalidWriteCount timedOut cancelled : Failure
  writeError flushError : Text → Failure

data State : Set where
  writing failed : List Byte → List Byte → State
  flushing complete : List Byte → State

-- Error information accompanies the terminal transition rather than being
-- erased by a generic failure status.
data WriteReply : Set where
  wrote : ℕ → WriteReply
  writeFailed : Text → WriteReply
  writeTimedOut writeCancelled : WriteReply

data FlushReply : Set where
  flushed : FlushReply
  flushFailed : Text → FlushReply
  flushTimedOut flushCancelled : FlushReply

Reply : State → Set
Reply (writing sent pending) = WriteReply
Reply (flushing sent) = FlushReply
Reply (complete sent) = ⊥
Reply (failed sent pending) = ⊥

record Result : Set where
  constructor result
  field state : State; reason : Maybe Failure

resume : List Byte → List Byte → State
resume sent [] = flushing sent
resume sent pending@(_ ∷ _) = writing sent pending

step : ∀ state → Reply state → Result
step (writing sent pending) (wrote zero) = result (failed sent pending) (just writeZero)
step (writing sent pending) (wrote (suc count)) with suc count ≤? length pending
... | no invalid = result (failed sent pending) (just invalidWriteCount)
... | yes valid = result (resume (sent ++ take (suc count) pending) (drop (suc count) pending)) nothing
step (writing sent pending) (writeFailed detail) = result (failed sent pending) (just (writeError detail))
step (writing sent pending) writeTimedOut = result (failed sent pending) (just timedOut)
step (writing sent pending) writeCancelled = result (failed sent pending) (just cancelled)
step (flushing sent) flushed = result (complete sent) nothing
step (flushing sent) (flushFailed detail) = result (failed sent []) (just (flushError detail))
step (flushing sent) flushTimedOut = result (failed sent []) (just timedOut)
step (flushing sent) flushCancelled = result (failed sent []) (just cancelled)
step (complete sent) ()
step (failed sent pending) ()

contents : State → List Byte
contents (writing sent pending) = sent ++ pending
contents (failed sent pending) = sent ++ pending
contents (flushing sent) = sent
contents (complete sent) = sent

resumeContents : ∀ sent pending → contents (resume sent pending) ≡ sent ++ pending
resumeContents sent [] = sym (++-identityʳ sent)
resumeContents sent (_ ∷ _) = refl

stepConserves : ∀ state reply → contents (Result.state (step state reply)) ≡ contents state
stepConserves (writing sent pending) (wrote zero) = refl
stepConserves (writing sent pending) (wrote (suc count)) with suc count ≤? length pending
... | no invalid = refl
... | yes valid = trans (resumeContents (sent ++ take (suc count) pending) (drop (suc count) pending))
  (trans (++-assoc sent (take (suc count) pending) (drop (suc count) pending))
    (cong (sent ++_) (take++drop≡id (suc count) pending)))
stepConserves (writing sent pending) (writeFailed detail) = refl
stepConserves (writing sent pending) writeTimedOut = refl
stepConserves (writing sent pending) writeCancelled = refl
stepConserves (flushing sent) flushed = refl
stepConserves (flushing sent) (flushFailed detail) = ++-identityʳ sent
stepConserves (flushing sent) flushTimedOut = ++-identityʳ sent
stepConserves (flushing sent) flushCancelled = ++-identityʳ sent
stepConserves (complete sent) ()
stepConserves (failed sent pending) ()

rank : State → ℕ
rank (writing sent pending) = suc (length pending)
rank (flushing sent) = 1
rank (complete sent) = 0
rank (failed sent pending) = 0

resumeRank : ∀ sent pending → rank (resume sent pending) ≡ suc (length pending)
resumeRank sent [] = refl
resumeRank sent (_ ∷ _) = refl

dropBound : ∀ n (bytes : List Byte) → length (drop n bytes) ≤ length bytes
dropBound n bytes = subst (_≤ length bytes) (sym (length-drop n bytes)) (m∸n≤m (length bytes) n)

stepDecreases : ∀ state reply → rank (Result.state (step state reply)) < rank state
stepDecreases (writing sent pending) (wrote zero) = s≤s z≤n
stepDecreases (writing sent []) (wrote (suc count)) = s≤s z≤n
stepDecreases (writing sent (byte ∷ pending)) (wrote (suc count)) with suc count ≤? suc (length pending)
... | no invalid = s≤s z≤n
... | yes valid rewrite resumeRank (sent ++ take (suc count) (byte ∷ pending)) (drop count pending) =
  s≤s (s≤s (dropBound count pending))
stepDecreases (writing sent pending) (writeFailed detail) = s≤s z≤n
stepDecreases (writing sent pending) writeTimedOut = s≤s z≤n
stepDecreases (writing sent pending) writeCancelled = s≤s z≤n
stepDecreases (flushing sent) flushed = ≤-refl
stepDecreases (flushing sent) (flushFailed detail) = ≤-refl
stepDecreases (flushing sent) flushTimedOut = ≤-refl
stepDecreases (flushing sent) flushCancelled = ≤-refl
stepDecreases (complete sent) ()
stepDecreases (failed sent pending) ()

Event = Σ State Reply

data Trace : State → List Event → State → Set where
  empty : ∀ state → Trace state [] state
  more : ∀ state reply {events final} → Trace (Result.state (step state reply)) events final →
    Trace state ((state , reply) ∷ events) final

traceConserves : ∀ {before events after} → Trace before events after → contents after ≡ contents before
traceConserves (empty state) = refl
traceConserves (more state reply rest) = trans (traceConserves rest) (stepConserves state reply)

finiteTrace : ∀ {before events after} → Trace before events after → length events ≤ rank before
finiteTrace (empty state) = z≤n
finiteTrace (more state reply rest) = ≤-trans (s≤s (finiteTrace rest)) (stepDecreases state reply)

initial : List Byte → State
initial = resume []

initialBound : ∀ bytes events after → Trace (initial bytes) events after → length events ≤ suc (length bytes)
initialBound bytes events after execution = subst (length events ≤_) (resumeRank [] bytes) (finiteTrace execution)

completedBytesExact : ∀ bytes events sent → Trace (initial bytes) events (complete sent) → sent ≡ bytes
completedBytesExact bytes events sent execution = trans (traceConserves execution) (resumeContents [] bytes)

failedCannotContinue : ∀ sent pending events after → Trace (failed sent pending) events after → events ≡ []
failedCannotContinue sent pending .[] .(failed sent pending) (empty _) = refl
failedCannotContinue sent pending events after (more _ () rest)

completedCannotContinue : ∀ sent events after → Trace (complete sent) events after → events ≡ []
completedCannotContinue sent .[] .(complete sent) (empty _) = refl
completedCannotContinue sent events after (more _ () rest)

isComplete : State → Bool
isComplete (complete sent) = true
isComplete _ = false

resumeIncomplete : ∀ sent pending → isComplete (resume sent pending) ≡ false
resumeIncomplete sent [] = refl
resumeIncomplete sent (_ ∷ _) = refl

flushReceipt : Event → Bool
flushReceipt (writing sent pending , reply) = false
flushReceipt (flushing sent , flushed) = true
flushReceipt (flushing sent , flushFailed detail) = false
flushReceipt (flushing sent , flushTimedOut) = false
flushReceipt (flushing sent , flushCancelled) = false
flushReceipt (complete sent , ())
flushReceipt (failed sent pending , ())

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

stepReceipt : ∀ state reply → isComplete (Result.state (step state reply)) ≡ true →
  flushReceipt (state , reply) ≡ true
stepReceipt (writing sent pending) (wrote zero) ()
stepReceipt (writing sent pending) (wrote (suc count)) completed with suc count ≤? length pending
... | no invalid with completed
...   | ()
stepReceipt (writing sent pending) (wrote (suc count)) completed | yes valid =
  ⊥-elim (falseNotTrue (trans (sym (resumeIncomplete (sent ++ take (suc count) pending) (drop (suc count) pending))) completed))
stepReceipt (writing sent pending) (writeFailed detail) ()
stepReceipt (writing sent pending) writeTimedOut ()
stepReceipt (writing sent pending) writeCancelled ()
stepReceipt (flushing sent) flushed completed = refl
stepReceipt (flushing sent) (flushFailed detail) ()
stepReceipt (flushing sent) flushTimedOut ()
stepReceipt (flushing sent) flushCancelled ()
stepReceipt (complete sent) () completed
stepReceipt (failed sent pending) () completed

completionReceipt : ∀ {before events bytes} → Trace before events (complete bytes) →
  isComplete before ≡ false → Any (λ event → flushReceipt event ≡ true) events
completionReceipt (empty .(complete _)) ()
completionReceipt (more state reply rest) incomplete with isComplete (Result.state (step state reply)) in completed
... | true = here (stepReceipt state reply completed)
... | false = there (completionReceipt rest completed)

successfulSendWasFlushed : ∀ bytes events sent → Trace (initial bytes) events (complete sent) →
  Any (λ event → flushReceipt event ≡ true) events
successfulSendWasFlushed bytes events sent execution = completionReceipt execution (resumeIncomplete [] bytes)
