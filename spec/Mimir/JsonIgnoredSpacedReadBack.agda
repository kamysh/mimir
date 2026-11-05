{-# OPTIONS --safe #-}
-- Arbitrarily nested ignored JSON values accept whitespace at each boundary.
import Mimir.FloatConversion
module Mimir.JsonIgnoredSpacedReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Bool using (true; false; not)
open import Data.List using ([]; _∷_; _++_)
open import Data.Product using (_,_; proj₁)
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
import Mimir.JsonIgnoredWhitespacePath as WhiteDependency
private
  module White = WhiteDependency floatConversion
import Mimir.JsonIgnoredKeyWhitespace as KeyDependency
private
  module Key = KeyDependency floatConversion
import Mimir.JsonIgnoredNumberReadBack as Character
import Mimir.JsonIgnoredValueSyntax as CompactDependency
private
  module Compact = CompactDependency floatConversion
import Mimir.JsonIgnoredSpacedSyntax as SyntaxDependency
private
  module Syntax = SyntaxDependency floatConversion
import Mimir.SerdeFlow as Flow
import Mimir.SerdeReadBack as Back

padding : ∀ {state input target suffix} → White.Skips state → ∀ before →
  (path : Path.Path state input target suffix) → White.Started path →
  Path.Path state (Syntax.Gap.bytes before ++ input) target suffix
padding skips before path positive = proj₁
  (White.spaces skips (Syntax.Gap.bytes before)
   (Syntax.Gap.valid before) path positive)

firstCore : ∀ frames item suffix →
  Path.Path (Step.value (Step.array ∷ frames)) (Syntax.core item suffix)
    (Step.boundary (Step.array ∷ frames) true) suffix →
  Path.Path (Step.boundary (Step.array ∷ frames) false) (Syntax.core item suffix)
    (Step.boundary (Step.array ∷ frames) true) suffix
firstCore frames item suffix receipt with Syntax.begins item suffix
... | Compact.leading byte rest exact stopped notClose = subst
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
  value frames (Syntax.value before item) suffix stopped =
    let path : _
        path = core frames item suffix stopped
    in padding (White.atValue frames) before path
       (White.different (λ ()) path)

  core : ∀ frames item suffix → Character.Stopped (Wire.text suffix) →
    Path.Path (Step.value frames) (Syntax.core item suffix) (Step.boundary frames true) suffix
  core frames Syntax.null suffix stopped = Scalar.null frames suffix
  core frames (Syntax.boolean choice) suffix stopped = Scalar.boolean frames choice suffix
  core frames (Syntax.string text) suffix stopped = Scalar.string frames (Compact.Quoted.body text)
    (Compact.Quoted.valid text) suffix
  core frames (Syntax.number bytes item exact) suffix stopped = Scalar.number frames (bytes ++ suffix) suffix item
    (Compact.numberText bytes item exact suffix) stopped
  core frames (Syntax.array items) suffix stopped = Path.append
    (Container.arrayOpen frames (Syntax.arrayBody true items suffix))
    (array frames true items suffix)
  core frames (Syntax.object members) suffix stopped = Path.append
    (Container.objectOpen frames
     (Syntax.objectBody true members suffix))
    (object frames true members suffix)

  array : ∀ frames first items suffix →
    Path.Path (Step.boundary (Step.array ∷ frames) (not first)) (Syntax.arrayBody first items suffix)
      (Step.boundary frames true) suffix
  array frames first (Syntax.itemsEnd before) suffix = padding (White.inContainer Step.array frames (not first)) before
    (Container.close Step.array frames (not first) suffix)
    White.started
  array frames true (Syntax.itemsMore before item items) suffix =
    let first : _
        first
          = firstValue frames item (Syntax.arrayBody false items suffix)
            (Syntax.arrayDelimiter items suffix)
        rest : _
        rest = array frames false items suffix
    in padding (White.inContainer Step.array frames false) before
       (Path.append first rest)
       (White.appendStarted first (White.different (λ ()) first) rest)
  array frames false (Syntax.itemsMore before item items) suffix =
    let first : _
        first
          = Container.comma Step.array frames
            (Syntax.spell item (Syntax.arrayBody false items suffix))
        rest : _
        rest
          = Path.append
            (value (Step.array ∷ frames) item
             (Syntax.arrayBody false items suffix)
             (Syntax.arrayDelimiter items suffix))
            (array frames false items suffix)
    in padding (White.inContainer Step.array frames true) before
       (Path.append first rest)
       (White.appendStarted first White.started rest)

  firstValue : ∀ frames item suffix → Character.Stopped (Wire.text suffix) →
    Path.Path (Step.boundary (Step.array ∷ frames) false) (Syntax.spell item suffix)
      (Step.boundary (Step.array ∷ frames) true) suffix
  firstValue frames (Syntax.value before item) suffix stopped =
    let path : _
        path
          = firstCore frames item suffix
            (core (Step.array ∷ frames) item suffix stopped)
    in padding (White.inContainer Step.array frames false) before path
       (White.different (λ ()) path)

  object : ∀ frames first members suffix →
    Path.Path (Step.boundary (Step.object ∷ frames) (not first)) (Syntax.objectBody first members suffix)
      (Step.boundary frames true) suffix
  object frames first (Syntax.membersEnd before) suffix = padding (White.inContainer Step.object frames (not first)) before
    (Container.close Step.object frames (not first) suffix)
    White.started
  object frames true (Syntax.membersMore before keyGap name colonGap item members) suffix =
    let first : _
        first
          = firstMember frames keyGap name colonGap item
            (Syntax.objectBody false members suffix)
            (Syntax.objectDelimiter members suffix)
        rest : _
        rest = object frames false members suffix
    in padding (White.inContainer Step.object frames false) before
       (Path.append first rest)
       (White.appendStarted first (White.different (λ ()) first) rest)
  object frames false (Syntax.membersMore before keyGap name colonGap item members) suffix =
    let first : _
        first
          = Container.comma Step.object frames
            (Syntax.fieldBytes keyGap name colonGap item
             (Syntax.objectBody false members suffix))
        rest : _
        rest
          = Path.append
            (member frames keyGap name colonGap item
             (Syntax.objectBody false members suffix)
             (Syntax.objectDelimiter members suffix))
            (object frames false members suffix)
    in padding (White.inContainer Step.object frames true) before
       (Path.append first rest)
       (White.appendStarted first White.started rest)

  member : ∀ frames keyGap name colonGap item suffix → Character.Stopped (Wire.text suffix) →
    Path.Path (Step.key (Step.object ∷ frames)) (Syntax.fieldBytes keyGap name colonGap item suffix)
      (Step.boundary (Step.object ∷ frames) true) suffix
  member frames keyGap name colonGap item suffix stopped =
    let path : _
        path = memberCore frames name colonGap item suffix stopped
    in padding (White.atKey (Step.object ∷ frames)) keyGap path
       (White.different (λ ()) path)

  firstMember : ∀ frames keyGap name colonGap item suffix → Character.Stopped (Wire.text suffix) →
    Path.Path (Step.boundary (Step.object ∷ frames) false) (Syntax.fieldBytes keyGap name colonGap item suffix)
      (Step.boundary (Step.object ∷ frames) true) suffix
  firstMember frames keyGap name colonGap item suffix stopped =
    let path : _
        path
          = Container.objectFirst frames _ suffix
            (memberCore frames name colonGap item suffix stopped)
    in padding (White.inContainer Step.object frames false) keyGap path
       (White.different (λ ()) path)

  memberCore : ∀ frames name colonGap item suffix → Character.Stopped (Wire.text suffix) →
    Path.Path (Step.key (Step.object ∷ frames)) (Syntax.memberBytes name colonGap item suffix)
      (Step.boundary (Step.object ∷ frames) true) suffix
  memberCore frames name colonGap item suffix stopped = Path.append
    (Key.key (Step.object ∷ frames) (Compact.Quoted.body name)
     (Compact.Quoted.valid name) (Syntax.Gap.bytes colonGap)
     (Syntax.Gap.valid colonGap) (Syntax.spell item suffix))
    (value (Step.object ∷ frames) item suffix stopped)

complete : ∀ item suffix → Character.Stopped (Wire.text suffix) →
  Back.Returned (Flow.lift (Run.read (Syntax.spell item suffix))) tt suffix
complete item suffix stopped = Path.closed (Syntax.spell item suffix) suffix
  (value [] item suffix stopped)
