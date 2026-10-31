{-# OPTIONS --safe #-}
-- Preserve the original byte prefix through component removal. Ignored empty
-- and '.' components do not become parent endpoints. Endpoints are bounded by
-- construction, so ancestor traversal terminates without fuel or truncation.
module Mimir.UnixPathParent where

open import Data.List using (List; []; _∷_; _++_; length; take)
open import Data.List.Properties using (++-assoc; ++-identityʳ; length-++-≤ˡ)
open import Data.Maybe using (Maybe; nothing; just; map)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-<-trans)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Fin using (Fin; fromℕ<; toℕ; inject≤)
open import Data.Fin.Properties using (toℕ<n)
open import Data.Product using (Σ; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; sym)
open import Induction.WellFounded using (Acc; acc)
open import Mimir.UnixPath
import Mimir.UnixPathParts as Parts

record Cursor (raw : Path) : Set where
  constructor cursor
  field
    ending : ℕ
    bounded : ending ≤ length raw
    previous : Maybe (Fin (length raw))

extendStrict : (raw addition : Path) → 0 < length addition → length raw < length (raw ++ addition)
extendStrict [] addition positive = positive
extendStrict (_ ∷ raw) addition positive = s≤s (extendStrict raw addition positive)

skip : ∀ raw addition → Cursor raw → Cursor (raw ++ addition)
skip raw addition (cursor ending bounded previous) = cursor ending
  (≤-trans bounded (length-++-≤ˡ raw {ys = addition}))
  (map (λ index → inject≤ index (length-++-≤ˡ raw {ys = addition})) previous)

remember : ∀ raw addition → 0 < length addition → Cursor raw → Cursor (raw ++ addition)
remember raw addition positive (cursor ending bounded previous) =
  cursor (length (raw ++ addition)) ≤-refl
    (just (fromℕ< (≤-<-trans bounded (extendStrict raw addition positive))))

meaningfulNonempty : ∀ path component → Parts.Meaning path (just component) → 0 < length path
meaningfulNonempty .(dot ∷ dot ∷ []) .parentDir Parts.parent = s≤s z≤n
meaningfulNonempty [] .(normal []) (Parts.ordinary nonempty _ _) = ⊥-elim (nonempty refl)
meaningfulNonempty (byte ∷ rest) .(normal (byte ∷ rest)) (Parts.ordinary _ _ _) = s≤s z≤n

firstChunk : ∀ raw chunk → Cursor raw → Cursor (raw ++ chunk)
firstChunk raw chunk state with part chunk | Parts.partSound chunk
... | nothing | _ = skip raw chunk state
... | just component | meaning = remember raw chunk (meaningfulNonempty chunk component meaning) state

nextChunk : ∀ raw chunk → Cursor raw → Cursor (raw ++ (slash ∷ chunk))
nextChunk raw chunk state with part chunk
... | nothing = skip raw (slash ∷ chunk) state
... | just _ = remember raw (slash ∷ chunk) (s≤s z≤n) state

scanTail : ∀ raw remaining → Cursor raw → Cursor (raw ++ separatedTail remaining)
scanTail raw [] state = subst Cursor (sym (++-identityʳ raw)) state
scanTail raw (chunk ∷ remaining) state =
  subst Cursor (++-assoc raw (slash ∷ chunk) (separatedTail remaining))
    (scanTail (raw ++ (slash ∷ chunk)) remaining (nextChunk raw chunk state))

scanChunks : ∀ raw groups → Cursor raw → Cursor (raw ++ renderChunks groups)
scanChunks raw (chunks first rest) state =
  subst Cursor (++-assoc raw first (separatedTail rest))
    (scanTail (raw ++ first) rest (firstChunk raw first state))

initial : ∀ origin → Cursor (prefix origin)
initial rooted = cursor 1 ≤-refl nothing
initial current = cursor 1 ≤-refl (just Data.Fin.zero)
initial relative = cursor 0 ≤-refl nothing

scanStart : (value : Start) → Cursor (renderStart value)
scanStart (start origin body) =
  subst Cursor (cong (prefix origin ++_) (splitExact body))
    (scanChunks (prefix origin) (split body) (initial origin))

scanPath : (path : Path) → Cursor path
scanPath path = subst Cursor (startExact path) (scanStart (splitStart path))

takeBound : (count : ℕ) (path : Path) → length (take count path) ≤ count
takeBound zero path = z≤n
takeBound (suc count) [] = z≤n
takeBound (suc count) (_ ∷ rest) = s≤s (takeBound count rest)

Parent : Path → Set
Parent path = Σ Path (λ shorter → length shorter < length path)

atEndpoint : ∀ path → Fin (length path) → Parent path
atEndpoint path index = take (toℕ index) path , ≤-<-trans (takeBound (toℕ index) path) (toℕ<n index)

parent : (path : Path) → Maybe (Parent path)
parent path = map (atEndpoint path) (Cursor.previous (scanPath path))

walk : (path : Path) → Acc _<_ (length path) → List Path
walk path (acc below) with parent path
... | nothing = path ∷ []
... | just (shorter , bound) = path ∷ walk shorter (below bound)

ancestors : Path → List Path
ancestors path = walk path (<-wellFounded (length path))

parents : Path → Maybe (List Path)
parents path with parent path
... | nothing = nothing
... | just (shorter , _) = just (ancestors shorter)
