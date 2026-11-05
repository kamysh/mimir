{-# OPTIONS --safe #-}
-- The iterative runner accepts every finite nested value in the compact grammar.
import Mimir.FloatConversion
module Mimir.JsonIgnoredValueReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Bool using (true; false; not)
open import Data.List using ([]; _∷_; _++_)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl; sym; subst)
import Mimir.ByteText as Wire
import Mimir.JsonIgnoredStep as StepDependency
private
  module Step = StepDependency floatConversion
import Mimir.JsonIgnoredRun as RunDependency
private
  module Run = RunDependency floatConversion
import Mimir.JsonIgnoredPath as PathDependency
private
  module Path = PathDependency floatConversion
import Mimir.JsonIgnoredScalarPath as ScalarDependency
private
  module Scalar = ScalarDependency floatConversion
import Mimir.JsonIgnoredContainerPath as ContainerDependency
private
  module Container = ContainerDependency floatConversion
import Mimir.JsonIgnoredNumberReadBack as Character
import Mimir.JsonIgnoredValueSyntax as SyntaxDependency
private
  module Syntax = SyntaxDependency floatConversion
import Mimir.SerdeFlow as Flow
import Mimir.SerdeReadBack as Back

firstArray : ∀ frames item suffix →
  Path.Path (Step.value (Step.array ∷ frames)) (Syntax.spell item suffix)
    (Step.boundary (Step.array ∷ frames) true) suffix →
  Path.Path (Step.boundary (Step.array ∷ frames) false) (Syntax.spell item suffix)
    (Step.boundary (Step.array ∷ frames) true) suffix
firstArray frames item suffix receipt with Syntax.begins item suffix
... | Syntax.leading byte rest exact stopped notClose = subst
  (λ input →
     Path.Path (Step.boundary (Step.array ∷ frames) false) input
     (Step.boundary (Step.array ∷ frames) true) suffix)
  (sym exact)
  (Container.arrayFirst frames byte rest suffix stopped notClose
   (subst
    (λ input →
       Path.Path (Step.value (Step.array ∷ frames)) input
       (Step.boundary (Step.array ∷ frames) true) suffix)
    exact receipt))

mutual
  value : ∀ frames item suffix → Character.Stopped (Wire.text suffix) →
    Path.Path (Step.value frames) (Syntax.spell item suffix) (Step.boundary frames true) suffix
  value frames Syntax.null suffix stopped = Scalar.null frames suffix
  value frames (Syntax.boolean choice) suffix stopped = Scalar.boolean frames choice suffix
  value frames (Syntax.string text) suffix stopped = Scalar.string frames (Syntax.Quoted.body text)
    (Syntax.Quoted.valid text) suffix
  value frames (Syntax.number bytes item exact) suffix stopped = Scalar.number frames (bytes ++ suffix) suffix item
    (Syntax.numberText bytes item exact suffix) stopped
  value frames (Syntax.array items) suffix stopped = Path.append
    (Container.arrayOpen frames (Syntax.arrayBody true items suffix))
    (array frames true items suffix)
  value frames (Syntax.object fields) suffix stopped = Path.append
    (Container.objectOpen frames
     (Syntax.objectBody true fields suffix))
    (object frames true fields suffix)

  array : ∀ frames first items suffix →
    Path.Path (Step.boundary (Step.array ∷ frames) (not first)) (Syntax.arrayBody first items suffix)
      (Step.boundary frames true) suffix
  array frames first [] suffix = Container.close Step.array frames (not first) suffix
  array frames true (item ∷ items) suffix = Path.append
    (firstArray frames item (Syntax.arrayBody false items suffix)
     (value (Step.array ∷ frames) item
      (Syntax.arrayBody false items suffix)
      (Syntax.arrayDelimiter items suffix)))
    (array frames false items suffix)
  array frames false (item ∷ items) suffix = Path.append
    (Container.comma Step.array frames
     (Syntax.spell item (Syntax.arrayBody false items suffix)))
    (Path.append
     (value (Step.array ∷ frames) item
      (Syntax.arrayBody false items suffix)
      (Syntax.arrayDelimiter items suffix))
     (array frames false items suffix))

  object : ∀ frames first fields suffix →
    Path.Path (Step.boundary (Step.object ∷ frames) (not first)) (Syntax.objectBody first fields suffix)
      (Step.boundary frames true) suffix
  object frames first [] suffix = Container.close Step.object frames (not first) suffix
  object frames true ((name , item) ∷ fields) suffix = Path.append
    (Container.objectFirst frames _
     (Syntax.objectBody false fields suffix)
     (member frames (name , item)
      (Syntax.objectBody false fields suffix)
      (Syntax.objectDelimiter fields suffix)))
    (object frames false fields suffix)
  object frames false (entry ∷ fields) suffix = Path.append
    (Container.comma Step.object frames
     (Syntax.fieldBytes entry (Syntax.objectBody false fields suffix)))
    (Path.append
     (member frames entry (Syntax.objectBody false fields suffix)
      (Syntax.objectDelimiter fields suffix))
     (object frames false fields suffix))

  member : ∀ frames entry suffix → Character.Stopped (Wire.text suffix) →
    Path.Path (Step.key (Step.object ∷ frames)) (Syntax.fieldBytes entry suffix)
      (Step.boundary (Step.object ∷ frames) true) suffix
  member frames (name , item) suffix stopped = Path.append
    (Container.key (Step.object ∷ frames) (Syntax.Quoted.body name)
     (Syntax.Quoted.valid name) (Syntax.spell item suffix))
    (value (Step.object ∷ frames) item suffix stopped)

complete : ∀ item suffix → Character.Stopped (Wire.text suffix) →
  Back.Returned (Flow.lift (Run.read (Syntax.spell item suffix))) tt suffix
complete item suffix stopped = Path.closed (Syntax.spell item suffix) suffix
  (value [] item suffix stopped)
