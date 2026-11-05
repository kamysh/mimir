{-# OPTIONS --safe #-}
-- Mimir's numbered-file rotation order and retained contents. The filesystem
-- supplies acknowledged remove/rename operations; their internals are external.
module Mimir.OperationalLogSteps where

open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; _++_; map; length; take)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _≤?_; z≤n; _⊓_)
open import Data.Nat.Properties using (≤-trans; +-monoʳ-≤; m⊓n≤n; ≤-irrelevant)
open import Data.List.Properties using (length-++; length-take)
open import Data.Vec using (Vec; []; _∷_; init; lookup; _[_]≔_)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
import Mimir.OperationalLogRetention as Log

empty : ∀ limit → Log.File limit
empty limit = Log.file [] z≤n

-- An empty slot denotes no retained contents, whether absent or empty.
-- Fin fixes the owned numbered filenames; unrelated paths are outside this view.
data Action (count : ℕ) : Set where
  remove : Fin count → Action count
  rename : Fin count → Fin count → Action count

apply : ∀ {limit count} → Action count → Vec (Log.File limit) count → Vec (Log.File limit) count
apply {limit} (remove slot) files = files [ slot ]≔ empty limit
apply {limit} (rename source target) files = (files [ target ]≔ lookup files source) [ source ]≔ empty limit

run : ∀ {limit count} → List (Action count) → Vec (Log.File limit) count → Vec (Log.File limit) count
run [] files = files
run (action ∷ rest) files = run rest (apply action files)

lift : ∀ {count} → Action count → Action (suc count)
lift (remove slot) = remove (suc slot)
lift (rename source target) = rename (suc source) (suc target)

rotation : ∀ archives → List (Action (suc archives))
rotation zero = remove zero ∷ []
rotation (suc archives) = map lift (rotation archives) ++ (rename zero (suc zero) ∷ [])

runAppend : ∀ {limit count} (first second : List (Action count)) (files : Vec (Log.File limit) count) →
  run (first ++ second) files ≡ run second (run first files)
runAppend [] second files = refl
runAppend (action ∷ first) second files = runAppend first second (apply action files)

runLift : ∀ {limit count} (actions : List (Action count)) (current : Log.File limit) (files : Vec (Log.File limit) count) →
  run (map lift actions) (current ∷ files) ≡ current ∷ run actions files
runLift [] current files = refl
runLift (remove slot ∷ actions) current files = runLift actions current (apply (remove slot) files)
runLift (rename source target ∷ actions) current files = runLift actions current (apply (rename source target) files)

rotationExact : ∀ {limit archives} (files : Log.State limit archives) →
  run (rotation archives) files ≡ empty limit ∷ init files
rotationExact {archives = zero} (current ∷ []) = refl
rotationExact {archives = suc archives} (current ∷ next ∷ files)
  rewrite runAppend (map lift (rotation archives)) (rename zero (suc zero) ∷ []) (current ∷ next ∷ files)
    | runLift (rotation archives) current (next ∷ files)
    | rotationExact (next ∷ files) = refl

appendCurrent : ∀ {limit archives} (files : Log.State limit archives) (bytes : List Log.Byte) →
  length (Log.File.bytes (Data.Vec.head files)) + length bytes ≤ limit → Log.State limit archives
appendCurrent (current ∷ previous) bytes fits =
  Log.file (Log.File.bytes current ++ bytes)
    (subst (_≤ _) (sym (length-++ (Log.File.bytes current))) fits) ∷ previous

fileEqual : ∀ {limit} (first second : Log.File limit) → Log.File.bytes first ≡ Log.File.bytes second → first ≡ second
fileEqual (Log.file bytes left) (Log.file .bytes right) refl rewrite ≤-irrelevant left right = refl

record Plan {limit archives} (entry : List Log.Byte) (before : Log.State limit archives) : Set where
  field
    actions : List (Action (suc archives))
    base : Log.State limit archives
    reachesBase : run actions before ≡ base
    fits : length (Log.File.bytes (Data.Vec.head base)) + length (Log.File.bytes (Log.clip limit entry)) ≤ limit

prepare : ∀ {limit archives} entry (before : Log.State limit archives) → Plan entry before
prepare {limit} {archives} entry before@(current ∷ previous)
  with (length (Log.File.bytes current) + length (Log.File.bytes (Log.clip limit entry))) ≤? limit
... | yes room = record { actions = [] ; base = before ; reachesBase = refl ; fits = room }
... | no full = record
  { actions = rotation archives ; base = empty limit ∷ init before ; reachesBase = rotationExact before
  ; fits = Log.File.bounded (Log.clip limit entry) }

planExact : ∀ {limit archives} entry (before : Log.State limit archives) →
  appendCurrent (Plan.base (prepare entry before)) (Log.File.bytes (Log.clip limit entry))
    (Plan.fits (prepare entry before)) ≡ Log.append entry before
planExact {limit} entry before@(current ∷ previous)
  with (length (Log.File.bytes current) + length (Log.File.bytes (Log.clip limit entry))) ≤? limit
... | yes room = refl
... | no full = cong (_∷ init before) (fileEqual _ _ refl)

prefixLength : ∀ count (bytes : List Log.Byte) → length (take count bytes) ≤ length bytes
prefixLength count bytes = subst (_≤ length bytes) (sym (length-take count bytes)) (m⊓n≤n count (length bytes))

partial : ∀ {limit archives} (entry : List Log.Byte) (before : Log.State limit archives) → ℕ → Log.State limit archives
partial {limit} entry before count = appendCurrent (Plan.base plan) (take count clipped)
  (≤-trans (+-monoʳ-≤ (length (Log.File.bytes (Data.Vec.head (Plan.base plan)))) (prefixLength count clipped)) (Plan.fits plan))
  where
  plan = prepare entry before
  clipped = Log.File.bytes (Log.clip limit entry)
