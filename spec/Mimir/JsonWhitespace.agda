{-# OPTIONS --safe #-}
-- JSON whitespace is exactly SP, HT, LF and CR, not Unicode White_Space.
-- The scanner preserves the maximal consumed prefix and the remaining bytes.
module Mimir.JsonWhitespace where

open import Data.Fin using (#_; _≟_)
open import Data.List using (List; []; _∷_; _++_)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All using (All)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Mimir.Bits using (Byte)

data Space : Byte → Set where
  sp : Space (# 32)
  ht : Space (# 9)
  lf : Space (# 10)
  cr : Space (# 13)

space? : ∀ byte → Dec (Space byte)
space? byte with byte ≟ (# 32)
... | yes refl = yes sp
... | no notSP with byte ≟ (# 9)
...   | yes refl = yes ht
...   | no notHT with byte ≟ (# 10)
...     | yes refl = yes lf
...     | no notLF with byte ≟ (# 13)
...       | yes refl = yes cr
...       | no notCR = no λ { sp → notSP refl ; ht → notHT refl ; lf → notLF refl ; cr → notCR refl }

Stopped : List Byte → Set
Stopped [] = ⊤
Stopped (first ∷ rest) = Space first → ⊥

record Run (input : List Byte) : Set where
  constructor run
  field
    prefix : List Byte
    spaces : All Space prefix
    rest : List Byte
    exact : input ≡ prefix ++ rest
    stopped : Stopped rest

take : ∀ input → Run input
take [] = run [] All.[] [] refl tt
take (byte ∷ input) with space? byte
... | no notSpace = run [] All.[] (byte ∷ input) refl notSpace
... | yes valid with take input
...   | run prefix spaces rest exact stopped = run (byte ∷ prefix) (valid All.∷ spaces) rest (cong (byte ∷_) exact) stopped

stoppedRun : ∀ input → Stopped input → Run.prefix (take input) ≡ [] × Run.rest (take input) ≡ input
stoppedRun [] stopped = refl , refl
stoppedRun (byte ∷ input) stopped with space? byte
... | no _ = refl , refl
... | yes valid = ⊥-elim (stopped valid)

complete : ∀ prefix → All Space prefix → ∀ rest → Stopped rest →
  Run.prefix (take (prefix ++ rest)) ≡ prefix × Run.rest (take (prefix ++ rest)) ≡ rest
complete [] All.[] rest stopped = stoppedRun rest stopped
complete (byte ∷ prefix) (valid All.∷ spaces) rest stopped with space? byte
... | no rejected = ⊥-elim (rejected valid)
... | yes admitted with take (prefix ++ rest) | complete prefix spaces rest stopped
...   | run consumed checked remaining exact terminal | samePrefix , sameRest = cong (byte ∷_) samePrefix , sameRest
