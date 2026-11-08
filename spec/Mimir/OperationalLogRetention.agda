{-# OPTIONS --safe #-}
-- Append-only operational evidence. Historical archives are left untouched.
module Mimir.OperationalLogRetention where

open import Data.Fin using (Fin)
open import Data.List using (List; _++_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)

Byte = Fin 256

record State : Set where
  constructor logFiles
  field
    current : List Byte
    archives : List (Text × List Byte)

append : List Byte → State → State
append entry before = logFiles (State.current before ++ entry) (State.archives before)

completeEntry : ∀ entry before →
  State.current (append entry before) ≡ State.current before ++ entry
completeEntry entry before = refl

archivesUnchanged : ∀ entry before →
  State.archives (append entry before) ≡ State.archives before
archivesUnchanged entry before = refl
