{-# OPTIONS --safe #-}
-- Field lookup commutes with the stored-JSON/schema translation. Byte-key
-- comparison and text comparison agree, and strict source ordering excludes
-- a later duplicate overriding the first stored lookup.
module Mimir.JsonSchemaLookup where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; subst)
import Mimir.ByteKeyOrder as Key
import Mimir.OrderedObject as Ordered
import Mimir.JsonStoredValue as Stored
import Mimir.JsonSchemaValue as Convert
import Mimir.DecodedKey as Decoded
import Mimir.StructuredValue as Schema
import Mimir.UnicodeText as Unicode

module M = Stored.Map
module S = Schema.Object

Admitted : M.Fields → Set
Admitted = All (λ { (name , value) → Stored.KeyValid name × Stored.Stored value })

NoKey : Key.Key → M.Fields → Set
NoKey name = All (λ { (other , value) → name ≢ other })

lowerExcludes : ∀ name fields → M.LowerBound name fields → NoKey name fields
lowerExcludes name [] All.[] = All.[]
lowerExcludes name ((other , value) ∷ rest) (before All.∷ tail) =
  (λ same → Key.irreflexive name (subst (name Key.<_) (Relation.Binary.PropositionalEquality.sym same) before))
    All.∷ lowerExcludes name rest tail

lookup : Key.Key → ∀ fields → Admitted fields → Maybe Schema.Value → Maybe Schema.Value
lookup queried [] All.[] fallback = fallback
lookup queried ((name , value) ∷ rest) ((key , admitted) All.∷ remaining) fallback with queried Ordered.≟Key name
... | yes same = just (Convert.convert value admitted)
... | no different = lookup queried rest remaining fallback

unrelatedWrites : ∀ {name} (queried : Stored.KeyValid name) fields admitted before → NoKey name fields →
  S.load (Convert.convertFields fields admitted) before (Decoded.text queried) ≡ before (Decoded.text queried)
unrelatedWrites queried [] All.[] before All.[] = refl
unrelatedWrites queried ((name , value) ∷ rest) ((key , admitted) All.∷ remaining) before (different All.∷ others) =
  trans (unrelatedWrites queried rest remaining
    (S.write (Decoded.text key) (Convert.convert value admitted) before) others)
    (S.otherField (Decoded.text key) (Decoded.text queried) (Convert.convert value admitted) before
      (λ same → different (Decoded.sameTextSameKey queried key same)))

lookupPreserved : ∀ {name} (queried : Stored.KeyValid name) fields admitted before → M.Sorted fields →
  S.load (Convert.convertFields fields admitted) before (Decoded.text queried) ≡
    lookup name fields admitted (before (Decoded.text queried))
lookupPreserved queried [] All.[] before M.empty = refl
lookupPreserved {queriedName} queried ((name , value) ∷ rest) ((key , admitted) All.∷ remaining) before
  (M.cons lower sorted) with queriedName Ordered.≟Key name
... | yes refl = trans (unrelatedWrites queried rest remaining
      (S.write (Decoded.text key) (Convert.convert value admitted) before) (lowerExcludes name rest lower))
    (trans (cong (S.write (Decoded.text key) (Convert.convert value admitted) before)
      (Decoded.sameKeySameText queried key refl))
      (S.ownField (Decoded.text key) (Convert.convert value admitted) before))
... | no different = trans (lookupPreserved queried rest remaining
      (S.write (Decoded.text key) (Convert.convert value admitted) before) sorted)
    (cong (lookup queriedName rest remaining)
      (S.otherField (Decoded.text key) (Decoded.text queried) (Convert.convert value admitted) before
        (λ same → different (Decoded.sameTextSameKey queried key same))))

normalizedLookupPreserved : ∀ {name} (queried : Stored.KeyValid name) fields admitted → M.Sorted fields →
  S.normalize (Convert.convertFields fields admitted) (Decoded.text queried) ≡ lookup name fields admitted nothing
normalizedLookupPreserved queried fields admitted sorted = lookupPreserved queried fields admitted S.empty sorted

textLookupPreserved : ∀ source (valid : Unicode.Valid source) fields admitted → M.Sorted fields →
  S.normalize (Convert.convertFields fields admitted) source ≡
    lookup (Decoded.Encoded.name (Decoded.fromText source valid)) fields admitted nothing
textLookupPreserved source valid fields admitted sorted = trans
  (cong (S.normalize (Convert.convertFields fields admitted)) (Relation.Binary.PropositionalEquality.sym
    (Decoded.Encoded.exact (Decoded.fromText source valid))))
  (normalizedLookupPreserved (Decoded.Encoded.valid (Decoded.fromText source valid)) fields admitted sorted)
