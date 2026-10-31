{-# OPTIONS --safe #-}
-- Lossy decoding consumes valid continuation bytes up to the first invalid
-- or missing byte. The invalid byte remains for the next replacement group.
module Mimir.UTF8LossyTail where

open import Data.Fin using (toℕ)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; zero; suc; _≤_; _≤?_; z≤n; s≤s)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_; _×-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Mimir.Bits using (Byte)

Between : ℕ → ℕ → Byte → Set
Between lower upper byte = lower ≤ toℕ byte × toℕ byte ≤ upper

between? : ∀ lower upper byte → Dec (Between lower upper byte)
between? lower upper byte = (lower ≤? toℕ byte) ×-dec (toℕ byte ≤? upper)

data Status : Set where complete interrupted : Status

data Tail : ℕ → ℕ → ℕ → List Byte → List Byte → List Byte → Status → Set where
  done : ∀ lower upper input → Tail lower upper zero input [] input complete
  exhausted : ∀ lower upper count → Tail lower upper (suc count) [] [] [] interrupted
  invalid : ∀ lower upper count byte input → ¬ Between lower upper byte →
    Tail lower upper (suc count) (byte ∷ input) [] (byte ∷ input) interrupted
  accepted : ∀ lower upper count byte input consumed remaining status → Between lower upper byte →
    Tail 128 191 count input consumed remaining status →
    Tail lower upper (suc count) (byte ∷ input) (byte ∷ consumed) remaining status

record Read (lower upper count : ℕ) (input : List Byte) : Set where
  constructor readResult
  field
    consumed remaining : List Byte
    status : Status
    meaning : Tail lower upper count input consumed remaining status

read : ∀ lower upper count input → Read lower upper count input
read lower upper zero input = readResult [] input complete (done lower upper input)
read lower upper (suc count) [] = readResult [] [] interrupted (exhausted lower upper count)
read lower upper (suc count) (byte ∷ input) with between? lower upper byte
... | no invalidByte = readResult [] (byte ∷ input) interrupted (invalid lower upper count byte input invalidByte)
... | yes validByte with read 128 191 count input
...   | readResult consumed remaining status meaning = readResult (byte ∷ consumed) remaining status
    (accepted lower upper count byte input consumed remaining status validByte meaning)

exact : ∀ {lower upper count input consumed remaining status} →
  Tail lower upper count input consumed remaining status → input ≡ consumed ++ remaining
exact (done lower upper input) = refl
exact (exhausted lower upper count) = refl
exact (invalid lower upper count byte input invalidByte) = refl
exact (accepted lower upper count byte input consumed remaining status validByte meaning) = cong (byte ∷_) (exact meaning)

lengthBound : ∀ {lower upper count input consumed remaining status} →
  Tail lower upper count input consumed remaining status → length consumed ≤ count
lengthBound (done lower upper input) = z≤n
lengthBound (exhausted lower upper count) = z≤n
lengthBound (invalid lower upper count byte input invalidByte) = z≤n
lengthBound (accepted lower upper count byte input consumed remaining status validByte meaning) = s≤s (lengthBound meaning)

completeLength : ∀ {lower upper count input consumed remaining} →
  Tail lower upper count input consumed remaining complete → length consumed ≡ count
completeLength (done lower upper input) = refl
completeLength (accepted lower upper count byte input consumed remaining .complete validByte meaning) = cong suc (completeLength meaning)

interruptedShort : ∀ {lower upper count input consumed remaining} →
  Tail lower upper count input consumed remaining interrupted → suc (length consumed) ≤ count
interruptedShort (exhausted lower upper count) = s≤s z≤n
interruptedShort (invalid lower upper count byte input invalidByte) = s≤s z≤n
interruptedShort (accepted lower upper count byte input consumed remaining .interrupted validByte meaning) = s≤s (interruptedShort meaning)

view : ∀ {lower upper count input} → Read lower upper count input → List Byte × List Byte × Status
view result = Read.consumed result , Read.remaining result , Read.status result

completeRead : ∀ {lower upper count input consumed remaining status} →
  Tail lower upper count input consumed remaining status →
  view (read lower upper count input) ≡ (consumed , remaining , status)
completeRead (done lower upper input) = refl
completeRead (exhausted lower upper count) = refl
completeRead (invalid lower upper count byte input invalidByte) with between? lower upper byte
... | no actual = refl
... | yes valid = ⊥-elim (invalidByte valid)
completeRead (accepted lower upper count byte input consumed remaining status validByte meaning)
  with between? lower upper byte
... | no invalidByte = ⊥-elim (invalidByte validByte)
... | yes actual with read 128 191 count input | completeRead meaning
...   | readResult .consumed .remaining .status checked | refl = refl

readerConserves : ∀ lower upper count input →
  input ≡ Read.consumed (read lower upper count input) ++ Read.remaining (read lower upper count input)
readerConserves lower upper count input = exact (Read.meaning (read lower upper count input))
