{-# OPTIONS --safe #-}
-- Typed-learning startup is a finite host-owned protocol. A Ready value
-- retains the actual checked catalogue/capability replies; it is independent
-- of the installed binary's version number and of model assertions.
module Mimir.JudgeHandshake where

open import Data.List using (List; []; _∷_; map)
import Data.Bool
import Data.List.Relation.Unary.All
open import Data.Nat using (ℕ; _≤_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; Σ; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (toList)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Mimir.Validation using (Fault; fault; unsupportedCombination)
import Mimir.StructuredValue as V
import Mimir.JudgeToolCatalogue as Catalogue
import Mimir.McpToolAdvertisement as Advertisement
import Mimir.LearningCapabilities as Capabilities
import Mimir.Effects as Effects

record CheckedCatalogue : Set where
  constructor checkedCatalogue
  field
    wire : V.Value
    advertised exposed : List V.Value
    covered : Catalogue.Covered advertised Catalogue.demands exposed
    accepted : Catalogue.admit wire ≡ inj₂ (advertised , exposed , covered)

data Effect : Set where
  initialize initializedNotification listTools learningCapabilities : Effect

Reply : Effect → Set
Reply initializedNotification = Fault ⊎ ⊤
Reply _ = Fault ⊎ V.Value

module E = Effects.Protocol Effect Reply
module Count = E.Counting (λ _ → 1)

module Contract (contractVersion assessmentModelVersion : ℕ) where
  record Ready : Set where
    constructor ready
    field
      catalogue : CheckedCatalogue
      wire : V.Value
      capabilities : Capabilities.Capabilities
      compatible : Capabilities.Compatible contractVersion assessmentModelVersion capabilities
      accepted : Capabilities.admit contractVersion assessmentModelVersion wire ≡ inj₂ (capabilities , compatible)

  Result = Fault ⊎ Ready

  CapabilityResult = Fault ⊎ Σ Capabilities.Capabilities (Capabilities.Compatible contractVersion assessmentModelVersion)

  finishCapabilities : ∀ catalogue wire (result : CapabilityResult) →
    Capabilities.admit contractVersion assessmentModelVersion wire ≡ result → E.Script Result
  finishCapabilities catalogue wire (inj₁ failure) checked = E.done (inj₁ failure)
  finishCapabilities catalogue wire (inj₂ (actual , compatible)) checked =
    E.done (inj₂ (ready catalogue wire actual compatible checked))

  afterCapabilities : CheckedCatalogue → Reply learningCapabilities → E.Script Result
  afterCapabilities catalogue (inj₁ failure) = E.done (inj₁ failure)
  afterCapabilities catalogue (inj₂ wire) = finishCapabilities catalogue wire
    (Capabilities.admit contractVersion assessmentModelVersion wire) refl

  CatalogueResult = Fault ⊎ Σ (List V.Value) (λ advertised →
    Σ (List V.Value) (Catalogue.Covered advertised Catalogue.demands))

  finishTools : ∀ wire (result : CatalogueResult) → Catalogue.admit wire ≡ result → E.Script Result
  finishTools wire (inj₁ failure) checked = E.done (inj₁ failure)
  finishTools wire (inj₂ (advertised , exposed , covered)) checked = E.ask learningCapabilities
    (afterCapabilities (checkedCatalogue wire advertised exposed covered checked))

  afterTools : Reply listTools → E.Script Result
  afterTools (inj₁ failure) = E.done (inj₁ failure)
  afterTools (inj₂ wire) = finishTools wire (Catalogue.admit wire) refl

  afterNotification : Reply initializedNotification → E.Script Result
  afterNotification (inj₁ failure) = E.done (inj₁ failure)
  afterNotification (inj₂ tt) = E.ask listTools afterTools

  afterInitialize : Reply initialize → E.Script Result
  afterInitialize (inj₁ failure) = E.done (inj₁ failure)
  afterInitialize (inj₂ wire) with Advertisement.stringEqual (toList "2024-11-05")
    (Advertisement.get (toList "protocolVersion") wire)
  ... | no unsupported = E.done (inj₁ (fault [] unsupportedCombination "unsupported MCP protocol"))
  ... | yes matched = E.ask initializedNotification afterNotification

  start : E.Script Result
  start = E.ask initialize afterInitialize

  finishCapabilitiesBound : ∀ catalogue wire result checked →
    Count.Bounded 0 (finishCapabilities catalogue wire result checked)
  finishCapabilitiesBound catalogue wire (inj₁ failure) checked = Count.done _
  finishCapabilitiesBound catalogue wire (inj₂ (actual , compatible)) checked = Count.done _

  capabilitiesBound : ∀ catalogue reply → Count.Bounded 0 (afterCapabilities catalogue reply)
  capabilitiesBound catalogue (inj₁ failure) = Count.done _
  capabilitiesBound catalogue (inj₂ wire) = finishCapabilitiesBound catalogue wire _ refl

  finishToolsBound : ∀ wire result checked → Count.Bounded 1 (finishTools wire result checked)
  finishToolsBound wire (inj₁ failure) checked = Count.done _
  finishToolsBound wire (inj₂ (advertised , exposed , covered)) checked =
    Count.ask learningCapabilities _ 0 ≤-refl (capabilitiesBound _)

  toolsBound : ∀ reply → Count.Bounded 1 (afterTools reply)
  toolsBound (inj₁ failure) = Count.done _
  toolsBound (inj₂ wire) = finishToolsBound wire _ refl

  notificationBound : ∀ reply → Count.Bounded 2 (afterNotification reply)
  notificationBound (inj₁ failure) = Count.done _
  notificationBound (inj₂ tt) = Count.ask listTools afterTools 1 ≤-refl toolsBound

  initializeBound : ∀ reply → Count.Bounded 3 (afterInitialize reply)
  initializeBound (inj₁ failure) = Count.done _
  initializeBound (inj₂ wire) with Advertisement.stringEqual (toList "2024-11-05")
    (Advertisement.get (toList "protocolVersion") wire)
  ... | no unsupported = Count.done _
  ... | yes matched = Count.ask initializedNotification afterNotification 2 ≤-refl notificationBound

  bounded : Count.Bounded 4 start
  bounded = Count.ask initialize afterInitialize 3 ≤-refl initializeBound

  completedUsesAtMostFourEvents : ∀ events result → E.Runs start events result → Count.count events ≤ 4
  completedUsesAtMostFourEvents events result execution = Count.runBounded bounded execution

  interruptionUsesAtMostFourEvents : ∀ events residual → E.Prefix start events residual → Count.count events ≤ 4
  interruptionUsesAtMostFourEvents events residual execution = Count.prefixBounded bounded execution

  rejectedCapabilitiesFinish : ∀ catalogue wire result checked failure →
    result ≡ inj₁ failure → finishCapabilities catalogue wire result checked ≡ E.done (inj₁ failure)
  rejectedCapabilitiesFinish catalogue wire (inj₁ failure) checked .failure refl = refl

  incompatibleCapabilitiesStop : ∀ catalogue wire failure →
    Capabilities.admit contractVersion assessmentModelVersion wire ≡ inj₁ failure →
    afterCapabilities catalogue (inj₂ wire) ≡ E.done (inj₁ failure)
  incompatibleCapabilitiesStop catalogue wire failure rejected =
    rejectedCapabilitiesFinish catalogue wire _ refl failure rejected

  sourceCoverageRequired : ∀ (permission : Ready) →
    Capabilities.Capabilities.sourceCoverage (Ready.capabilities permission) ≡ Data.Bool.true
  sourceCoverageRequired permission = Capabilities.acceptedSupportsCoverage contractVersion assessmentModelVersion
    (Ready.capabilities permission) (Ready.compatible permission)

  originalCatalogueDefinitions : ∀ (permission : Ready) →
    Data.List.Relation.Unary.All.All (Catalogue.Published (CheckedCatalogue.advertised (Ready.catalogue permission)))
      (CheckedCatalogue.exposed (Ready.catalogue permission))
  originalCatalogueDefinitions permission = Catalogue.everyPublishedDefinitionChecked
    (CheckedCatalogue.covered (Ready.catalogue permission))

  effectNames : List E.Event → List Effect
  effectNames = map proj₁

  finishCapabilityEffects : ∀ catalogue wire result checked events permission →
    E.Runs (finishCapabilities catalogue wire result checked) events (inj₂ permission) →
    effectNames events ≡ []
  finishCapabilityEffects catalogue wire (inj₁ failure) checked events permission ()
  finishCapabilityEffects catalogue wire (inj₂ (actual , compatible)) checked .[] ._ (E.returned _) = refl

  capabilityEffects : ∀ catalogue reply events permission →
    E.Runs (afterCapabilities catalogue reply) events (inj₂ permission) → effectNames events ≡ []
  capabilityEffects catalogue (inj₁ failure) events permission ()
  capabilityEffects catalogue (inj₂ wire) events permission execution =
    finishCapabilityEffects catalogue wire _ refl events permission execution

  finishToolEffects : ∀ wire result checked events permission →
    E.Runs (finishTools wire result checked) events (inj₂ permission) →
    effectNames events ≡ learningCapabilities ∷ []
  finishToolEffects wire (inj₁ failure) checked events permission ()
  finishToolEffects wire (inj₂ (advertised , exposed , covered)) checked
    .((learningCapabilities , reply) ∷ events) permission
    (E.replied .learningCapabilities _ reply {events} rest) =
    cong (learningCapabilities ∷_) (capabilityEffects _ reply events permission rest)

  toolEffects : ∀ reply events permission → E.Runs (afterTools reply) events (inj₂ permission) →
    effectNames events ≡ learningCapabilities ∷ []
  toolEffects (inj₁ failure) events permission ()
  toolEffects (inj₂ wire) events permission execution = finishToolEffects wire _ refl events permission execution

  notificationEffects : ∀ reply events permission → E.Runs (afterNotification reply) events (inj₂ permission) →
    effectNames events ≡ listTools ∷ learningCapabilities ∷ []
  notificationEffects (inj₁ failure) events permission ()
  notificationEffects (inj₂ tt) .((listTools , reply) ∷ events) permission
    (E.replied .listTools _ reply {events} rest) =
    cong (listTools ∷_) (toolEffects reply events permission rest)

  initializeEffects : ∀ reply events permission → E.Runs (afterInitialize reply) events (inj₂ permission) →
    effectNames events ≡ initializedNotification ∷ listTools ∷ learningCapabilities ∷ []
  initializeEffects (inj₁ failure) events permission ()
  initializeEffects (inj₂ wire) events permission execution with
    Advertisement.stringEqual (toList "2024-11-05") (Advertisement.get (toList "protocolVersion") wire)
  ... | no unsupported with execution
  ...   | ()
  initializeEffects (inj₂ wire) .((initializedNotification , reply) ∷ events) permission
    (E.replied .initializedNotification _ reply {events} rest) | yes matched =
    cong (initializedNotification ∷_) (notificationEffects reply events permission rest)

  successfulStartupOrder : ∀ events permission → E.Runs start events (inj₂ permission) →
    effectNames events ≡ initialize ∷ initializedNotification ∷ listTools ∷ learningCapabilities ∷ []
  successfulStartupOrder .((initialize , reply) ∷ events) permission
    (E.replied .initialize _ reply {events} rest) =
    cong (initialize ∷_) (initializeEffects reply events permission rest)
