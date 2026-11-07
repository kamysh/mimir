{-# OPTIONS --safe #-}
-- Evidence enrichment preserves retrieval order, ranks each belief's grounding
-- edges strongest-first, caps before fetching chunks, and caches both present
-- and absent chunk reads for the duration of one enriched query.
module Mimir.EvidenceRead where

open import Data.Bool using (Bool; true; false; not)
open import Data.Float.Base using (Float; _<ᵇ_)
open import Data.List using (List; []; _∷_; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (does)
open import Mimir.Text using (Text; trim)
import Mimir.ApplicationStore as Store
import Mimir.DocumentStore as Documents
import Mimir.CandidateGraph as G
import Mimir.RetrievalRanking as Ranking
import Mimir.PosteriorComputation as Lookup
import Mimir.Effects as Effects

record Reference : Set where
  constructor reference
  field chunk : ℕ; document : Text; section : List Text; snippet : Text; weight : Float

record Grounded : Set where
  constructor grounded
  field belief : G.BeliefValues; evidence : List Reference

referenceOf : Float → Documents.Chunk → Reference
referenceOf weight c = reference (Documents.Chunk.identity c) (Documents.Chunk.document c)
  (Documents.Chunk.section c) (trim (Documents.Chunk.content c)) weight

ranked : ℕ → Ranking.Selection → List Store.Ground → List Store.Ground
ranked belief limit grounds = Ranking.cap limit (Ranking.sort
  (λ a b → not (Store.Ground.weight a <ᵇ Store.Ground.weight b))
  (filterᵇ (λ e → does (belief ≟ Store.Ground.belief e)) grounds))

Cache = List (ℕ × Maybe Documents.Chunk)

data Effect : Set where
  readGrounds : List ℕ → Effect
  readChunk : ℕ → Effect

Reply : Effect → Set
Reply (readGrounds ids) = Text ⊎ List Store.Ground
Reply (readChunk id) = Text ⊎ Maybe Documents.Chunk

module E = Effects.Protocol Effect Reply
open E

References = Text ⊎ (List Reference × Cache)

prepend : Float → Maybe Documents.Chunk → References → References
prepend weight nothing result = result
prepend weight (just chunk) (inj₁ error) = inj₁ error
prepend weight (just chunk) (inj₂ (refs , cache)) = inj₂ (referenceOf weight chunk ∷ refs , cache)

refs : List Store.Ground → Cache → Script References
refs [] cache = done (inj₂ ([] , cache))
refs (edge ∷ rest) cache with Lookup.lookup (Store.Ground.chunk edge) cache
... | just cached = refs rest cache >>= λ result → done (prepend (Store.Ground.weight edge) cached result)
... | nothing = ask (readChunk (Store.Ground.chunk edge)) (λ
  { (inj₁ error) → done (inj₁ error)
  ; (inj₂ observed) → refs rest ((Store.Ground.chunk edge , observed) ∷ cache) >>= λ result →
      done (prepend (Store.Ground.weight edge) observed result) })

enrich : Ranking.Selection → List Store.Ground → List G.BeliefValues → Cache → Script (Text ⊎ List Grounded)
enrich limit grounds [] cache = done (inj₂ [])
enrich limit grounds (belief ∷ rest) cache = refs (ranked (G.BeliefValues.identity belief) limit grounds) cache >>= λ
  { (inj₁ error) → done (inj₁ error)
  ; (inj₂ (evidence , after)) → enrich limit grounds rest after >>= λ
      { (inj₁ error) → done (inj₁ error)
      ; (inj₂ later) → done (inj₂ (grounded belief evidence ∷ later)) } }

uncached : List Store.Ground → Script (Text ⊎ List Reference)
uncached [] = done (inj₂ [])
uncached (edge ∷ rest) = ask (readChunk (Store.Ground.chunk edge)) (λ
  { (inj₁ error) → done (inj₁ error)
  ; (inj₂ observed) → uncached rest >>= λ
      { (inj₁ error) → done (inj₁ error)
      ; (inj₂ later) → done (append observed later) } })
  where
  append : Maybe Documents.Chunk → List Reference → Text ⊎ List Reference
  append nothing later = inj₂ later
  append (just chunk) later = inj₂ (referenceOf (Store.Ground.weight edge) chunk ∷ later)

one : ℕ → Ranking.Selection → Script (Text ⊎ List Reference)
one belief limit = ask (readGrounds (belief ∷ [])) (λ
  { (inj₁ error) → done (inj₁ error)
  ; (inj₂ grounds) → uncached (ranked belief limit grounds) })

many : Ranking.Selection → List G.BeliefValues → Script (Text ⊎ List Grounded)
many limit [] = done (inj₂ [])
many limit beliefs@(_ ∷ _) = ask (readGrounds (Data.List.map G.BeliefValues.identity beliefs)) (λ
  { (inj₁ error) → done (inj₁ error) ; (inj₂ grounds) → enrich limit grounds beliefs [] })
