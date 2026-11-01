{-# OPTIONS --safe #-}
-- Subprocess supervision: concurrent stdin/stdout/stderr, complete stdout,
-- bounded diagnostic retention and process-group cleanup before reaping. Signals
-- are requests to the OS; they are not claims that every descendant terminated.
module Mimir.JudgeProcess where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_; _++_; length; take)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤_; _<_; _≤?_; _+_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String; toList)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Bits using (Byte)
open import Mimir.Text using (Text)
import Mimir.SourceFailure as Source
import Mimir.Effects as Effects

data Stream : Set where stdout stderr : Stream
-- Diagnostic storage is bounded; the stderr pipe is still fully drained.
diagnosticLimit : ℕ
diagnosticLimit = 64 * 1024 where open import Data.Nat using (_*_)

retain : Stream → List Byte → List Byte
retain stdout value = value
retain stderr value = take diagnosticLimit value

record Chunk : Set where
  constructor chunk
  field bytes : List Byte; bounded : length bytes ≤ 8192; nonempty : 0 < length bytes

data Failure : Set where
  nativeFailure : Text → Failure
  unsuccessfulExit : Text → List Byte → Failure

Result = Failure ⊎ List Byte

record Buffers : Set where
  constructor buffers
  field inputClosed outputClosed diagnosticClosed : Bool
        output diagnostic : List Byte

initial : Buffers
initial = buffers false false false [] []

closed : Buffers → Bool
closed b = Buffers.inputClosed b ∧ Buffers.outputClosed b ∧ Buffers.diagnosticClosed b

isClosed : Stream → Buffers → Bool
isClosed stdout = Buffers.outputClosed
isClosed stderr = Buffers.diagnosticClosed

bytes : Stream → Buffers → List Byte
bytes stdout = Buffers.output
bytes stderr = Buffers.diagnostic

set : Stream → List Byte → Buffers → Buffers
set stdout value b = record b { output = value }
set stderr value b = record b { diagnostic = value }

close : Stream → Buffers → Buffers
close stdout b = record b { outputClosed = true }
close stderr b = record b { diagnosticClosed = true }

-- Each poll is a scheduler observation from the three concurrent futures.
-- Futures already completed cannot produce another read/write event.
data IO (b : Buffers) : Set where
  inputWrittenAndShutdown : Buffers.inputClosed b ≡ false → IO b
  received : (stream : Stream) → isClosed stream b ≡ false → Chunk → IO b
  eof : (stream : Stream) → isClosed stream b ≡ false → IO b
  failed : Text → IO b

record Exit : Set where
  constructor exit
  field success : Bool; display : Text

record Spawn : Set where
  constructor spawnSpec
  field program : Text; arguments : List Text; directory : Text; input : List Byte

data Effect : Set where
  -- spawn uses piped stdio, kill_on_drop(true), and setpgid(0,0) before exec.
  spawn : Spawn → Effect
  takeStdin takeStdout takeStderr : ℕ → Effect
  poll : ℕ → Buffers → Effect
  signalGroup startKillChild : ℕ → Effect
  wait : ℕ → Effect

Reply : Effect → Set
Reply (spawn _) = Text ⊎ ℕ
Reply (takeStdin _) = Bool
Reply (takeStdout _) = Bool
Reply (takeStderr _) = Bool
Reply (poll _ b) = IO b
Reply (signalGroup _) = ⊤ -- kill(-pid, SIGKILL), error ignored
Reply (startKillChild _) = ⊤ -- direct child cleanup, error ignored
Reply (wait _) = Text ⊎ Exit
module P = Effects.Protocol Effect Reply
open P using (Script; done; ask; _>>=_)

data State : Set where
  running : Spawn → ℕ → Buffers → State
  executing : Script State → State
  finished : Result → State

-- Once wait returns a status, group ownership is cleared. No later cleanup
-- can target that possibly reused group ID. Unreaped cleanup is attempted by
-- the Drop guard as well, exactly as in the native ownership object.
dropOwned : ℕ → Result → Script State
dropOwned pid result = ask (signalGroup pid) (λ _ → ask (startKillChild pid) (λ _ → done (finished result)))

afterCleanupWait : ℕ → Result → Reply (wait 0) → Script State
afterCleanupWait pid result (inj₂ status) = done (finished result)
afterCleanupWait pid result _ = dropOwned pid result

cleanup : ℕ → Result → Script State
cleanup pid result = ask (signalGroup pid) (λ _ →
  ask (wait pid) (afterCleanupWait pid result))

afterWait : ℕ → Buffers → Reply (wait 0) → Script State
afterWait pid b (inj₁ detail) = cleanup pid (inj₁ (nativeFailure detail))
afterWait pid b (inj₂ status) with Exit.success status
... | true = done (finished (inj₂ (Buffers.output b)))
... | false = done (finished (inj₁ (unsuccessfulExit (Exit.display status) (Buffers.diagnostic b))))

reap : ℕ → Buffers → Script State
reap pid b = ask (signalGroup pid) (λ _ → ask (wait pid) (afterWait pid b))

continue : Spawn → ℕ → Buffers → State
continue request pid b with closed b
... | false = running request pid b
... | true = executing (reap pid b)

afterIO : (request : Spawn) → (pid : ℕ) → (b : Buffers) → IO b → State
afterIO request pid b (inputWrittenAndShutdown _) = continue request pid (record b { inputClosed = true })
afterIO request pid b (eof stream _) = continue request pid (close stream b)
afterIO request pid b (received stream _ new) =
  continue request pid (set stream (retain stream (bytes stream b ++ Chunk.bytes new)) b)
afterIO request pid b (failed detail) = executing (cleanup pid (inj₁ (nativeFailure detail)))

takePipes : Spawn → ℕ → Script State
takePipes request pid = ask (takeStdin pid) λ where
  false → dropOwned pid (inj₁ (nativeFailure (toList "harness stdin unavailable")))
  true → ask (takeStdout pid) λ where
    false → dropOwned pid (inj₁ (nativeFailure (toList "harness stdout unavailable")))
    true → ask (takeStderr pid) λ where
      false → dropOwned pid (inj₁ (nativeFailure (toList "harness stderr unavailable")))
      true → done (running request pid initial)

start : Spawn → State
start request = executing (ask (spawn request) λ where
    (inj₁ detail) → done (finished (inj₁ (nativeFailure detail)))
    (inj₂ pid) → takePipes request pid)

data Step : Set where
  internal : State → Step
  external : (effect : Effect) → (Reply effect → State) → Step
  stopped : Result → Step

next : State → Step
next (running request pid b) = external (poll pid b) (afterIO request pid b)
next (executing (done state)) = internal state
next (executing (ask effect k)) = external effect (λ reply → executing (k reply))
next (finished result) = stopped result

data Transition : State → Maybe P.Event → State → Set where
  internalStep : ∀ {before after} → next before ≡ internal after → Transition before nothing after
  externalStep : ∀ {before effect k} → next before ≡ external effect k →
    (reply : Reply effect) → Transition before (just (effect , reply)) (k reply)
  cancelled : ∀ request pid b → Transition (running request pid b) nothing
    (executing (dropOwned pid (inj₁ (nativeFailure (toList "cancelled")))))

data Trace : State → List (Maybe P.Event) → State → Set where
  empty : ∀ {state} → Trace state [] state
  step : ∀ {before middle after event events} → Transition before event middle →
    Trace middle events after → Trace before (event ∷ events) after

-- Retaining stderr never imposes a limit on successful model output.
stdoutComplete : ∀ before part → retain stdout (before ++ part) ≡ before ++ part
stdoutComplete before part = refl

reapedCannotSignalAgain : ∀ pid result status →
  afterCleanupWait pid result (inj₂ status) ≡ done (finished result)
reapedCannotSignalAgain pid result status = refl

-- Ownership at an arbitrary async cancellation point is computed from actual
-- spawn/wait receipts. This covers cancellation while writing, reading or
-- waiting, including cancellation of an unfinished future.
ownerAfter : Maybe ℕ → List (Maybe P.Event) → Maybe ℕ
ownerAfter owner [] = owner
ownerAfter owner (just (spawn request , inj₂ pid) ∷ rest) = ownerAfter (just pid) rest
ownerAfter owner (just (wait pid , inj₂ status) ∷ rest) = ownerAfter nothing rest
ownerAfter owner (_ ∷ rest) = ownerAfter owner rest

cancelOwned : Maybe ℕ → Script State
cancelOwned nothing = done (finished (inj₁ (nativeFailure (toList "cancelled"))))
cancelOwned (just pid) = dropOwned pid (inj₁ (nativeFailure (toList "cancelled")))
