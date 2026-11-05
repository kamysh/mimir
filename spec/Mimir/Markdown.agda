{-# OPTIONS --safe #-}
-- The current Mimir section language: a heading starts at column zero, has
-- one or more '#' characters, and is followed by ASCII space or end of line.
-- This is not a claim of implementing the complete CommonMark grammar.
module Mimir.Markdown where

open import Data.Char using (Char; _≟_)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; reverse; map)
open import Data.List.Properties using (unfold-reverse)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_; _<?_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text; trim; Nonempty; cons)
open import Mimir.DocumentStore using (Chunk; mkChunk)

-- Rust str::lines recognizes LF and CRLF, omits the final empty segment, and
-- does not treat a bare CR as a separator.
dropCR : Text → Text
dropCR [] = []
dropCR (c ∷ cs) with c ≟ '\r'
... | yes _ = cs
... | no _ = c ∷ cs

scanLines : Text → Text → List Text
scanLines [] [] = []
scanLines current@(_ ∷ _) [] = reverse current ∷ []
scanLines current (c ∷ cs) with c ≟ '\n'
... | yes _ = reverse (dropCR current) ∷ scanLines [] cs
... | no _ = scanLines (c ∷ current) cs

lines : Text → List Text
lines = scanLines []

hashes : ℕ → Text → ℕ × Text
hashes depth [] = depth , []
hashes depth (c ∷ cs) with c ≟ '#'
... | yes _ = hashes (suc depth) cs
... | no _ = depth , (c ∷ cs)

record Heading : Set where
  constructor heading
  field depth : ℕ; title : Text

classify : Text → Maybe Heading
classify text with hashes 0 text
... | zero , rest = nothing
... | suc depth , [] = just (heading (suc depth) [])
... | suc depth , (c ∷ cs) with c ≟ ' '
...   | yes _ = just (heading (suc depth) (trim (c ∷ cs)))
...   | no _ = nothing

record Frame : Set where
  constructor frame
  field depth identity : ℕ; title : Text

-- Newest enclosing heading first; this is reverse order to the Rust Vec.
parents : ℕ → List Frame → List Frame
parents depth [] = []
parents depth (f ∷ fs) with Frame.depth f <? depth
... | yes _ = f ∷ fs
... | no _ = parents depth fs

parentIsShallower : ∀ depth stack f fs → parents depth stack ≡ f ∷ fs → Frame.depth f < depth
parentIsShallower depth [] f fs ()
parentIsShallower depth (g ∷ gs) f fs same with Frame.depth g <? depth
... | yes less with same
...   | refl = less
parentIsShallower depth (g ∷ gs) f fs same | no _ = parentIsShallower depth gs f fs same

parentID : List Frame → Maybe ℕ
parentID [] = nothing
parentID (f ∷ fs) = just (Frame.identity f)

record Parser : Set where
  constructor parser
  field
    completed : List Chunk
    stack : List Frame
    currentID nextAllocation : ℕ
    section : List Text
    parent : Maybe ℕ
    buffer : Text
open Parser

module Parse (document : Text) (project : Maybe Text) (supply : ℕ → ℕ) where
  initial : Parser
  initial = parser [] [] (supply 0) 1 [] nothing []

  flush : Parser → Parser
  flush s with trim (buffer s)
  ... | [] = parser (completed s) (stack s) (currentID s) (nextAllocation s) (section s) (parent s) []
  ... | content@(_ ∷ _) = parser
    (mkChunk (currentID s) document (section s) content (parent s) project ∷ completed s)
    (stack s) (currentID s) (nextAllocation s) (section s) (parent s) []

  beginHeading : Parser → Heading → Text → Parser
  beginHeading s h line = parser (completed (flush s))
    (frame (Heading.depth h) (supply (nextAllocation s)) (Heading.title h) ∷ enclosing)
    (supply (nextAllocation s)) (suc (nextAllocation s))
    (map Frame.title (reverse enclosing) ++ (Heading.title h ∷ []))
    (parentID enclosing) (line ++ ('\n' ∷ []))
    where enclosing = parents (Heading.depth h) (stack s)

  appendLine : Parser → Text → Parser
  appendLine s line = parser (completed s) (stack s) (currentID s) (nextAllocation s)
    (section s) (parent s) (buffer s ++ (line ++ ('\n' ∷ [])))

  process : Parser → Text → Parser
  process s line with classify line
  ... | nothing = appendLine s line
  ... | just h = beginHeading s h line

  scan : Parser → List Text → Parser
  scan s [] = flush s
  scan s (line ∷ rest) = scan (process s line) rest

  parse : Text → List Chunk
  parse text = reverse (completed (scan initial (lines text)))

  -- Blank sections do not consume a stored-chunk slot, while heading allocation
  -- still occurs. Allocation supply is explicit; no UUID-uniqueness axiom is used.
  emptyFlushPreservesChunks : ∀ s → trim (buffer s) ≡ [] → completed (flush s) ≡ completed s
  emptyFlushPreservesChunks s empty rewrite empty = refl

  headingParentFromStack : ∀ s h line →
    parent (beginHeading s h line) ≡ parentID (parents (Heading.depth h) (stack s))
  headingParentFromStack s h line = refl

  headingAllocatesOnce : ∀ s h line →
    nextAllocation (beginHeading s h line) ≡ suc (nextAllocation s)
  headingAllocatesOnce s h line = refl

  ordinaryLineKeepsIdentity : ∀ s line → currentID (appendLine s line) ≡ currentID s
  ordinaryLineKeepsIdentity s line = refl

  ChunkValid : Chunk → Set
  ChunkValid c = Chunk.document c ≡ document ×
    (Chunk.project c ≡ project × Nonempty (Chunk.content c))

  flushValid : ∀ s → All ChunkValid (completed s) → All ChunkValid (completed (flush s))
  flushValid s valid with trim (buffer s)
  ... | [] = valid
  ... | c ∷ cs = (refl , (refl , cons c cs)) ∷ valid

  processValid : ∀ s line → All ChunkValid (completed s) →
    All ChunkValid (completed (process s line))
  processValid s line valid with classify line
  ... | nothing = valid
  ... | just h = flushValid s valid

  scanValid : ∀ s input → All ChunkValid (completed s) →
    All ChunkValid (completed (scan s input))
  scanValid s [] valid = flushValid s valid
  scanValid s (line ∷ rest) valid = scanValid (process s line) rest (processValid s line valid)

  appendValid : ∀ {xs ys} → All ChunkValid xs → All ChunkValid ys → All ChunkValid (xs ++ ys)
  appendValid [] right = right
  appendValid (p ∷ ps) right = p ∷ appendValid ps right

  reverseValid : ∀ {xs} → All ChunkValid xs → All ChunkValid (reverse xs)
  reverseValid [] = []
  reverseValid {x ∷ xs} (p ∷ ps) rewrite unfold-reverse x xs = appendValid (reverseValid ps) (p ∷ [])

  everyChunkHasOriginalMetadata : ∀ text → All ChunkValid (parse text)
  everyChunkHasOriginalMetadata text = reverseValid (scanValid initial (lines text) [])
