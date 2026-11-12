{-# OPTIONS --safe #-}
module Mimir.LearningCorrections where

open import Data.List using (List; []; map)
open import Data.Maybe using (Maybe)
open import Mimir.UUIDGroups using (UUID; _≟UUID_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.SourceSchema using (Source; source; Provenance; userFeedback; agentReport; toolResult)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.LearningSchema using (Kind; estimate; decision; suggestion; LearningItem)
open import Mimir.ExperienceSchema using (Experience)
open import Mimir.ReviewSchema using (Review)
open import Mimir.Collections using (pairEqual; maybeEqual)
open import Mimir.Validation
import Mimir.Retention as Retention

provenanceEqual : (x y : Provenance) → Dec (x ≡ y)
provenanceEqual userFeedback userFeedback = yes refl
provenanceEqual userFeedback agentReport = no (λ ())
provenanceEqual userFeedback toolResult = no (λ ())
provenanceEqual agentReport userFeedback = no (λ ())
provenanceEqual agentReport agentReport = yes refl
provenanceEqual agentReport toolResult = no (λ ())
provenanceEqual toolResult userFeedback = no (λ ())
provenanceEqual toolResult agentReport = no (λ ())
provenanceEqual toolResult toolResult = yes refl

SourceKey = Text × (Text × (Text × (Provenance × Maybe Text)))

sourceKey : Source → SourceKey
sourceKey s = Source.reference s , Source.actor s , Source.text s , Source.provenance s , Source.recordedAt s

sourceKeyEqual : (x y : SourceKey) → Dec (x ≡ y)
sourceKeyEqual = pairEqual _≟Text_ (pairEqual _≟Text_ (pairEqual _≟Text_
  (pairEqual provenanceEqual (maybeEqual _≟Text_))))

kindEqual : (x y : Kind) → Dec (x ≡ y)
kindEqual estimate estimate = yes refl
kindEqual estimate decision = no (λ ())
kindEqual estimate suggestion = no (λ ())
kindEqual decision estimate = no (λ ())
kindEqual decision decision = yes refl
kindEqual decision suggestion = no (λ ())
kindEqual suggestion estimate = no (λ ())
kindEqual suggestion decision = no (λ ())
kindEqual suggestion suggestion = yes refl

ItemKey = UUID × (Text × (Text × (Text × Kind)))

itemKey : LearningItem → ItemKey
itemKey i = LearningItem.identity i , LearningItem.reference i , LearningItem.actor i ,
  LearningItem.statement i , LearningItem.kind i

itemKeyEqual : (x y : ItemKey) → Dec (x ≡ y)
itemKeyEqual = pairEqual _≟UUID_ (pairEqual _≟Text_ (pairEqual _≟Text_ (pairEqual _≟Text_ kindEqual)))

module SourceRetention = Retention.Elements SourceKey sourceKeyEqual
module ItemRetention = Retention.Elements ItemKey itemKeyEqual

ExperienceCorrection : Experience → Experience → Set
ExperienceCorrection old new = Experience.project old ≡ Experience.project new ×
  SourceRetention.Retained (map sourceKey (Experience.sources old)) (map sourceKey (Experience.sources new))

validateExperienceCorrection : ∀ old new → Checked (ExperienceCorrection old new)
validateExperienceCorrection old new = combine
  (at (key "project") (check (fault [] wrongIdentity "experience project is immutable")
    (Experience.project old ≟Text Experience.project new)))
  (at (key "source_records") (SourceRetention.validate
    (map sourceKey (Experience.sources old)) (map sourceKey (Experience.sources new))))

ReviewCorrection : Review → Review → Set
ReviewCorrection old new = ItemRetention.Retained
  (map itemKey (Review.extracted old)) (map itemKey (Review.extracted new))

validateReviewCorrection : ∀ old new → Checked (ReviewCorrection old new)
validateReviewCorrection old new = at (key "extracted_items") (ItemRetention.validate
  (map itemKey (Review.extracted old)) (map itemKey (Review.extracted new)))

reviewCorrectionsCompose : ∀ first second third →
  ReviewCorrection first second → ReviewCorrection second third → ReviewCorrection first third
reviewCorrectionsCompose first second third = ItemRetention.transitive

-- Conditions and predictions may be revised; this does not authorize changing
-- the attributed quote, its kind, its source reference, actor, or item identity.
interpretationMayChange : ∀ item conditions predictions →
  itemKey (record item { conditions = conditions ; predictions = predictions }) ≡ itemKey item
interpretationMayChange item conditions predictions = refl
