{-# OPTIONS --safe #-}
-- Belief-specific field priority at the MCP text boundary. The classification
-- requires content, id, alpha and beta; ordinary object order is preserved.
-- The priority operation carries an entry-conservation proof.
module Mimir.AgentFieldOrder where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Mimir.JsonStoredValue as JSON
import Mimir.McpEnvelope as Envelope
import Mimir.ByteKeyOrder as Key
import Mimir.PriorityFields as Priority

module P = Priority.For JSON.Value

firstFields : List Key.Key
firstFields = Envelope.literal "content" ∷ Envelope.literal "id" ∷ Envelope.literal "project" ∷
  Envelope.literal "memory_type" ∷ Envelope.literal "probability" ∷ Envelope.literal "confidence" ∷
  Envelope.literal "created_at" ∷ Envelope.literal "last_activated_at" ∷ Envelope.literal "evidence" ∷ []

posteriorFields : List Key.Key
posteriorFields = Envelope.literal "alpha" ∷ Envelope.literal "beta" ∷
  Envelope.literal "alpha0" ∷ Envelope.literal "beta0" ∷ []

contains : Key.Key → JSON.Map.Fields → Bool
contains name fields with JSON.Map.lookup name fields
... | nothing = false
... | just value = true

isBelief : JSON.Map.Fields → Bool
isBelief fields = contains (Envelope.literal "content") fields ∧ contains (Envelope.literal "id") fields ∧
  contains (Envelope.literal "alpha") fields ∧ contains (Envelope.literal "beta") fields

order : ∀ fields → P.Reordered fields
order fields with isBelief fields
... | false = P.reordered fields Perm.refl
... | true = P.reorder firstFields posteriorFields fields

preservesEntries : ∀ fields → P.Reordered.fields (order fields) Perm.↭ fields
preservesEntries fields = P.Reordered.exact (order fields)

ordinaryOrderUnchanged : ∀ fields → isBelief fields ≡ false → P.Reordered.fields (order fields) ≡ fields
ordinaryOrderUnchanged fields notBelief rewrite notBelief = refl
