{-# OPTIONS --safe #-}
-- Independent ordered extraction relation for provider calls. A syntactically
-- invalid argument remains attached to its original ID/name; only envelope
-- errors or duplicate IDs reject collection.
module Mimir.ProviderCollection where

open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Mimir.Text using (Text)
import Mimir.ProviderResponse as Response
import Mimir.ProviderQueue as Provider
import Mimir.SelectiveTraversal as Selective
import Mimir.Validation
import Mimir.StructuredValue

module Collection (arguments : Text → Mimir.Validation.Fault Data.Sum.⊎ Mimir.StructuredValue.Value) where
  module D = Response.Decode arguments
  module Q = Response.Q

  module For (read : Mimir.StructuredValue.Value → Mimir.Validation.Fault Data.Sum.⊎ Data.Maybe.Maybe Q.Call) where
    module Extraction = Selective.Traversal Mimir.StructuredValue.Value Q.Call Mimir.Validation.Fault read

    data Collected : List Text → List Mimir.StructuredValue.Value → List Q.Call → Set where
      empty : ∀ {seen} → Collected seen [] []
      ignored : ∀ {seen entry rest values} → read entry ≡ inj₂ nothing →
        Collected seen rest values → Collected seen (entry ∷ rest) values
      retained : ∀ {seen entry request rest values} → read entry ≡ inj₂ (just request) →
        Provider.IDs.Absent (Q.Call.identity request) seen →
        Collected (Q.Call.identity request ∷ seen) rest values →
        Collected seen (entry ∷ rest) (request ∷ values)

    sound : ∀ seen entries values → D.collect read seen entries ≡ inj₂ values → Collected seen entries values
    sound seen [] .[] refl = empty
    sound seen (entry ∷ rest) values observed with read entry in decoded
    ... | inj₁ failure with observed
    ...   | ()
    sound seen (entry ∷ rest) values observed | inj₂ nothing = ignored decoded (sound seen rest values observed)
    sound seen (entry ∷ rest) values observed | inj₂ (just request)
      with Provider.IDs.absent? (Q.Call.identity request) seen
    ... | no repeated with observed
    ...   | ()
    sound seen (entry ∷ rest) values observed | inj₂ (just request) | yes absent
      with D.collect read (Q.Call.identity request ∷ seen) rest in tail
    ... | inj₁ failure with observed
    ...   | ()
    sound seen (entry ∷ rest) .(request ∷ values) refl | inj₂ (just request) | yes absent | inj₂ values =
      retained decoded absent (sound (Q.Call.identity request ∷ seen) rest values tail)

    complete : ∀ {seen entries values} → Collected seen entries values → D.collect read seen entries ≡ inj₂ values
    complete empty = refl
    complete (ignored decoded rest) rewrite decoded = complete rest
    complete (retained {seen} {request = request} decoded absent rest) rewrite decoded
      with Provider.IDs.absent? (Q.Call.identity request) seen
    ... | no impossible = ⊥-elim (impossible absent)
    ... | yes checked rewrite complete rest = refl

    preservesExtraction : ∀ {seen entries values} → Collected seen entries values → Extraction.Extracted entries values
    preservesExtraction empty = Extraction.empty
    preservesExtraction (ignored decoded rest) = Extraction.ignored decoded (preservesExtraction rest)
    preservesExtraction (retained decoded absent rest) = Extraction.retained decoded (preservesExtraction rest)

    allUnseen : ∀ {seen entries values} → Collected seen entries values →
      All (λ request → Provider.IDs.Absent (Q.Call.identity request) seen) values
    allUnseen empty = []
    allUnseen (ignored decoded rest) = allUnseen rest
    allUnseen (retained decoded absent rest) = absent ∷ removeHead (allUnseen rest)
      where
      removeHead : ∀ {identity seen values} → All (λ request → Provider.IDs.Absent (Q.Call.identity request) (identity ∷ seen)) values →
        All (λ request → Provider.IDs.Absent (Q.Call.identity request) seen) values
      removeHead [] = []
      removeHead ((different ∷ absent) ∷ tail) = absent ∷ removeHead tail

    invertHead : ∀ {identity seen values} → All (λ request → Provider.IDs.Absent (Q.Call.identity request) (identity ∷ seen)) values →
      Provider.IDs.Absent identity (map Q.Call.identity values)
    invertHead [] = []
    invertHead ((different ∷ absent) ∷ rest) = (λ same → different (sym same)) ∷ invertHead rest

    unique : ∀ {seen entries values} → Collected seen entries values → Provider.IDs.Unique (map Q.Call.identity values)
    unique empty = tt
    unique (ignored decoded rest) = unique rest
    unique (retained decoded absent rest) = invertHead (allUnseen rest) , unique rest
