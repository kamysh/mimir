{-# OPTIONS --safe #-}
-- Coupled chunk/vector storage and replacement. Physical AGE and pgvector
-- projections must be committed in one transaction; these laws describe the
-- paired state that the SQL implementation must refine.
module Mimir.DocumentStore where

open import Data.Char using (_≟_)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.List.Properties using (≡-dec; length-++)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Nat.Properties using (+-suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using (Vec)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym)
open import Mimir.Text using (Text)

record Chunk : Set where
  constructor mkChunk
  field
    identity : ℕ
    document : Text
    section : List Text
    content : Text
    parent : Maybe ℕ
    project : Maybe Text
open Chunk

-- The submitting agent's source reference. Its explanation is retained as an
-- assertion of support, without a numerical weight or a claim of proven truth.
record Citation : Set where
  constructor citation
  field chunk : ℕ; document quotation explanation : Text

-- Equality compares the stored source reference itself, including its original
-- explanation; an old candidate key cannot silently acquire a new declaration.
citationEqual : (first second : Citation) → Relation.Nullary.Dec (first ≡ second)
citationEqual (citation id path quotedText why) (citation other actual words reason)
  with Data.Nat._≟_ id other | ≡-dec Data.Char._≟_ path actual |
    ≡-dec Data.Char._≟_ quotedText words | ≡-dec Data.Char._≟_ why reason
... | yes refl | yes refl | yes refl | yes refl = yes refl
... | no different | _ | _ | _ = no (λ { refl → different refl })
... | _ | no different | _ | _ = no (λ { refl → different refl })
... | _ | _ | no different | _ = no (λ { refl → different refl })
... | _ | _ | _ | no different = no (λ { refl → different refl })

module Storage (Scalar : Set) (dimension : ℕ) where
  Vector = Vec Scalar dimension

  record Stored : Set where
    constructor stored
    field chunk : Chunk; embedding : Vector

  Store = List Stored

  graphView : Store → List Chunk
  graphView = map Stored.chunk

  vectorView : Store → List (ℕ × Vector)
  vectorView = map (λ entry → identity (Stored.chunk entry) , Stored.embedding entry)

  -- This includes empty stores and arbitrary prior replacements/deletions.
  projectionsAgree : ∀ store → map identity (graphView store) ≡ map proj₁ (vectorView store)
  projectionsAgree [] = refl
  projectionsAgree (entry ∷ rest) = cong (identity (Stored.chunk entry) ∷_) (projectionsAgree rest)

  align : List Chunk → List Vector → Maybe Store
  align [] [] = just []
  align [] (_ ∷ _) = nothing
  align (_ ∷ _) [] = nothing
  align (c ∷ cs) (v ∷ vs) with align cs vs
  ... | nothing = nothing
  ... | just entries = just (stored c v ∷ entries)

  alignCounts : ∀ chunks vectors entries → align chunks vectors ≡ just entries →
    (length chunks ≡ length vectors) × (length entries ≡ length chunks)
  alignCounts [] [] .[] refl = refl , refl
  alignCounts [] (_ ∷ _) entries ()
  alignCounts (_ ∷ _) [] entries ()
  alignCounts (c ∷ cs) (v ∷ vs) entries proof with align cs vs in tail
  ... | nothing with proof
  ...   | ()
  alignCounts (c ∷ cs) (v ∷ vs) entries proof | just rest with proof
  ... | refl with alignCounts cs vs rest tail
  ...   | counts , sizes = cong suc counts , cong suc sizes

  wrongCountRejected : ∀ chunks vectors → length chunks ≢ length vectors →
    align chunks vectors ≡ nothing
  wrongCountRejected chunks vectors different with align chunks vectors in result
  ... | nothing = refl
  ... | just entries = ⊥-elim (different (proj₁ (alignCounts chunks vectors entries result)))

  clear : Text → Store → Store
  clear path [] = []
  clear path (entry ∷ rest) with ≡-dec _≟_ path (document (Stored.chunk entry))
  ... | yes _ = clear path rest
  ... | no _ = entry ∷ clear path rest

  matching : Text → Store → Store
  matching path [] = []
  matching path (entry ∷ rest) with ≡-dec _≟_ path (document (Stored.chunk entry))
  ... | yes _ = entry ∷ matching path rest
  ... | no _ = matching path rest

  clearIdempotent : ∀ path entries → clear path (clear path entries) ≡ clear path entries
  clearIdempotent path [] = refl
  clearIdempotent path (entry ∷ rest) with ≡-dec _≟_ path (document (Stored.chunk entry))
  ... | yes _ = clearIdempotent path rest
  ... | no different with ≡-dec _≟_ path (document (Stored.chunk entry))
  ...   | yes same = ⊥-elim (different same)
  ...   | no _ = cong (entry ∷_) (clearIdempotent path rest)

  clearRemovesAllMatches : ∀ path entries → matching path (clear path entries) ≡ []
  clearRemovesAllMatches path [] = refl
  clearRemovesAllMatches path (entry ∷ rest) with ≡-dec _≟_ path (document (Stored.chunk entry))
  ... | yes _ = clearRemovesAllMatches path rest
  ... | no different with ≡-dec _≟_ path (document (Stored.chunk entry))
  ...   | yes same = ⊥-elim (different same)
  ...   | no _ = clearRemovesAllMatches path rest

  replace : Text → Store → Store → Store
  replace path proposed before = proposed ++ clear path before

  partitionCount : ∀ path entries →
    length (matching path entries) + length (clear path entries) ≡ length entries
  partitionCount path [] = refl
  partitionCount path (entry ∷ rest) with ≡-dec _≟_ path (document (Stored.chunk entry))
  ... | yes _ = cong suc (partitionCount path rest)
  ... | no _ = trans (+-suc (length (matching path rest)) (length (clear path rest)))
    (cong suc (partitionCount path rest))

  matchingAppend : ∀ path first second →
    matching path (first ++ second) ≡ matching path first ++ matching path second
  matchingAppend path [] second = refl
  matchingAppend path (entry ∷ rest) second with ≡-dec _≟_ path (document (Stored.chunk entry))
  ... | yes _ = cong (entry ∷_) (matchingAppend path rest second)
  ... | no _ = matchingAppend path rest second

  otherDocumentSurvivesClear : ∀ path other entries → path ≢ other →
    matching other (clear path entries) ≡ matching other entries
  otherDocumentSurvivesClear path other [] different = refl
  otherDocumentSurvivesClear path other (entry ∷ rest) different
    with ≡-dec _≟_ path (document (Stored.chunk entry)) | ≡-dec _≟_ other (document (Stored.chunk entry))
  ... | yes same | yes also = ⊥-elim (different (trans same (sym also)))
  ... | yes same | no notOther = otherDocumentSurvivesClear path other rest different
  ... | no notPath | yes same with ≡-dec _≟_ other (document (Stored.chunk entry))
  ...   | yes _ = cong (entry ∷_) (otherDocumentSurvivesClear path other rest different)
  ...   | no differentEntry = ⊥-elim (differentEntry same)
  otherDocumentSurvivesClear path other (entry ∷ rest) different | no notPath | no notOther
    with ≡-dec _≟_ other (document (Stored.chunk entry))
  ... | yes same = ⊥-elim (notOther same)
  ... | no _ = otherDocumentSurvivesClear path other rest different

  foreignNewEntriesAbsent : ∀ path other entries → path ≢ other →
    All (λ entry → path ≡ document (Stored.chunk entry)) entries → matching other entries ≡ []
  foreignNewEntriesAbsent path other [] different [] = refl
  foreignNewEntriesAbsent path other (entry ∷ rest) different (same ∷ allSame)
    with ≡-dec _≟_ other (document (Stored.chunk entry))
  ... | yes also = ⊥-elim (different (trans same (sym also)))
  ... | no _ = foreignNewEntriesAbsent path other rest different allSame

  otherDocumentSurvivesReplacement : ∀ path other proposed before → path ≢ other →
    All (λ entry → path ≡ document (Stored.chunk entry)) proposed →
    matching other (replace path proposed before) ≡ matching other before
  otherDocumentSurvivesReplacement path other proposed before different allSame
    rewrite matchingAppend other proposed (clear path before)
      | foreignNewEntriesAbsent path other proposed different allSame =
    otherDocumentSurvivesClear path other before different

  data Outcome : Set where prepareFailed transactionAborted commitReceipt commitLost : Outcome

  record Publication : Set where
    constructor published
    field durable : Store; confirmed : Maybe ℕ

  -- Preparation includes parsing, complete embedding response validation, and
  -- ID/provenance checks. Nothing is removed before this succeeds.
  publish : Text → Store → Store → Outcome → Publication
  publish path proposed before prepareFailed = published before nothing
  publish path proposed before transactionAborted = published before nothing
  publish path proposed before commitReceipt = published (replace path proposed before) (just (length proposed))
  publish path proposed before commitLost = published (replace path proposed before) nothing

  failedPreparationPreserves : ∀ path proposed before →
    Publication.durable (publish path proposed before prepareFailed) ≡ before
  failedPreparationPreserves path proposed before = refl

  failedTransactionPreserves : ∀ path proposed before →
    Publication.durable (publish path proposed before transactionAborted) ≡ before
  failedTransactionPreserves path proposed before = refl

  confirmedCountIsStoredCount : ∀ path proposed before →
    Publication.confirmed (publish path proposed before commitReceipt) ≡ just (length proposed)
  confirmedCountIsStoredCount path proposed before = refl

  publicationKeepsProjectionsTogether : ∀ path proposed before result →
    map identity (graphView (Publication.durable (publish path proposed before result))) ≡
    map proj₁ (vectorView (Publication.durable (publish path proposed before result)))
  publicationKeepsProjectionsTogether path proposed before result =
    projectionsAgree (Publication.durable (publish path proposed before result))
