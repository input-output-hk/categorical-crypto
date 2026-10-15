{-# OPTIONS --safe --without-K --guardedness #-}

-- The quarter-error security steps come from finite initialization laws, not
-- weakening exact comparisons. A fixed passive cap ignores version tags, so
-- the same steps also bound the honest fault observation independently.

open import Categories.Category
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Construction.Quotient

open import Data.Bool.Base
open import Data.Empty
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ; ½)
open import Data.Rational.Properties
open import Relation.Binary.PropositionalEquality
open import Data.Sum.Base
open import Function.Base using (id)
open import Function.Bundles
open import Level using (0ℓ)
open import Relation.Nullary.Negation

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.Examples.FaultFlag
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.Machine.Wire
open import CategoricalCrypto.UC.Model.Enrichment
open import CategoricalCrypto.UC.Model.Graded
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.RandomSystems.Advantage
open import CategoricalCrypto.UC.RandomSystems.Composition
open import CategoricalCrypto.UC.RandomSystems.Availability
open import CategoricalCrypto.UC.RandomSystems.Construction
open import CategoricalCrypto.UC.RandomSystems.Quantitative
open import CategoricalCrypto.UC.RandomSystems.Seal

import CategoricalCrypto.UC.Model.Setup as PM
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.Examples.FaultFlag.UC where

private
  module G = MonoidalCategory 𝔾ᵒ
  module P = Category 𝒫ᴵ
  module Q = MonoidalCongruence congᴿ
  variable ε : ℚ

realᵒ middleᵒ idealᵒ : ifaceᵒ unitᴵ PM.⇒ PM.T₀ (ifaceᵒ Advᴵ) (ifaceᵒ Honᴵ)
realᵒ = gradedᵒ real
middleᵒ = gradedᵒ middle
idealᵒ = gradedᵒ ideal

simᵒ : ifaceᵒ Advᴵ PM.ℐ.⇒ ifaceᵒ Advᴵ
simᵒ = procᵒ simulator

private
  first-factor : gradedᵒ (cache quarter original) G.≈ PM.sub simᵒ PM.∘ middleᵒ
  first-factor = G.Equiv.trans (≈ᴹ⇒≈ᵍ (cache-simulates quarter previous))
    (G.Equiv.sym (sub-gradedᵒ simulator middle))

  second-factor : gradedᵒ (cache (returnₚ false) previous) G.≈ PM.sub simᵒ PM.∘ idealᵒ
  second-factor = G.Equiv.trans
    (≈ᴹ⇒≈ᵍ (P.Equiv.trans (cache-simulates (returnₚ false) latest)
      (P.∘-resp-≈ʳ (false-cache-clean latest))))
    (G.Equiv.sym (sub-gradedᵒ simulator ideal))

  first-bound : realᵒ ∼ᴿ[ ¼ ] (PM.sub simᵒ PM.∘ middleᵒ)
  first-bound = Approximation.≈[]-mono approxᵒ (≤-reflexive (+-identityʳ ¼))
    (Approximation.≈[]-trans approxᵒ
      (gradedᵒ-≈ᴿ[] (half-quarter-cache original)) (≈⇒∼ᴿ[0] first-factor))

  second-bound : middleᵒ ∼ᴿ[ ¼ ] (PM.sub simᵒ PM.∘ idealᵒ)
  second-bound = Approximation.≈[]-mono approxᵒ (≤-reflexive (+-identityʳ ¼))
    (Approximation.≈[]-trans approxᵒ
      (gradedᵒ-≈ᴿ[] (quarter-false-cache previous)) (≈⇒∼ᴿ[0] second-factor))

  raw-bound : (s : ifaceᵒ Advᴵ PM.ℐ.⇒ ifaceᵒ Advᴵ)
             → realᵒ ∼ᴿ[ ε ] (PM.sub s PM.∘ idealᵒ)
             → real ≈ᴿ[ ε ] P._∘_ (subᴵ {A = Honᴵ} (unprocᵒ s)) ideal
  raw-bound {ε} s e = ungradedᵒ-∼ᴿ[]
    (Approximation.≈[]-mono approxᵒ (≤-reflexive (+-identityʳ ε))
      (Approximation.≈[]-trans approxᵒ e (≈⇒∼ᴿ[0] factor)))
    where
    factor : (PM.sub s PM.∘ idealᵒ) G.≈ gradedᵒ (P._∘_ (subᴵ {A = Honᴵ} (unprocᵒ s)) ideal)
    factor = G.Equiv.trans
      (G.∘-resp-≈ˡ (G.⊗.F-resp-≈ (G.Equiv.sym (procᵒ-unprocᵒ s) , G.Equiv.refl)))
      (sub-gradedᵒ (unprocᵒ s) ideal)

first-security : realᵒ ≤UCᴿ[ ¼ ] middleᵒ
first-security = Constructs⇒≤UCᴿ[] {f = realᵒ} {g = middleᵒ} (simᵒ , first-bound)

second-security : middleᵒ ≤UCᴿ[ ¼ ] idealᵒ
second-security = Constructs⇒≤UCᴿ[] {f = middleᵒ} {g = idealᵒ} (simᵒ , second-bound)

composed-security : realᵒ ≤UCᴿ[ ¼ ℚ.+ ¼ ] idealᵒ
composed-security = ≤UCᴿ[]-trans {f = realᵒ} {g = middleᵒ} {h = idealᵒ} first-security second-security

half-security : realᵒ ≤UCᴿ[ ½ ] idealᵒ
half-security = composed-security

composed-simulator : proj₁ composed-security ≡ simᵒ PM.ℐ.∘ simᵒ
composed-simulator = refl

composed-simulator-image : proj₁ composed-security G.≈ procᵒ doubleSimulator
composed-simulator-image = G.Equiv.sym (procᵒ-∘ simulator simulator)

composed-error-positive : 0ℚ ℚ.< (¼ ℚ.+ ¼)
composed-error-positive = +-mono-< 0<¼ 0<¼

security-condition : Constructs ½ realᵒ idealᵒ
security-condition = ≤UCᴿ[]⇒Constructs {f = realᵒ} {g = idealᵒ} half-security

no-small-construction : ε ℚ.< ½ → ¬ (Constructs ε realᵒ idealᵒ)
no-small-construction small (s , e) = no-small-simulation small (unprocᵒ s) (raw-bound s e)

no-small-security : ε ℚ.< ½ → ¬ (realᵒ ≤UCᴿ[ ε ] idealᵒ)
no-small-security {ε} small w = no-small-construction small
  (≤UCᴿ[]⇒Constructs {ε = ε} {f = realᵒ} {g = idealᵒ} w)

------------------------------------------------------------------------
-- A fixed passive mode retains the honest initialization error
------------------------------------------------------------------------

private
  module MC = Core (𝒱ₚ 0ℓ)
  module S = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

passiveᴹ : Proc Advᴵ 𝟭ᴵ
passiveᴹ = MC.mk MC.Iˢ λ where
  (_ , inj₁ _) → botₚ
  (_ , inj₂ ())

passive : ifaceᵒ Advᴵ G.⇒ G.unit
passive = procᵘ passiveᴹ

passive-simulator : (passive G.∘ simᵒ) G.≈ passive
passive-simulator = G.Equiv.trans (G.Equiv.sym (procᵘ-∘ passiveᴹ simulator))
  (≈ᴹ⇒≈ᵘ (∘-wireᴹ {Advᴵ} {Advᴵ} {𝟭ᴵ} previousTag id passiveᴹ
    S.○ᴹ S.≲⇒≈ᴹ (S.mk-cong λ where
      (_ , inj₁ _) → bot-bind-≈ₚ _
      (_ , inj₂ ()))))

first-full : QAvailabilityᴿ.SecureAvailable ¼ ¼ passive passive realᵒ middleᵒ
first-full = QAvailabilityᴿ.secure-mode-preserving
  {s = simᵒ} {f = realᵒ} {g = middleᵒ} (Q.≈⇒∼ passive-simulator) (proj₂ first-security)

second-full : QAvailabilityᴿ.SecureAvailable ¼ ¼ passive passive middleᵒ idealᵒ
second-full = QAvailabilityᴿ.secure-mode-preserving
  {s = simᵒ} {f = middleᵒ} {g = idealᵒ} (Q.≈⇒∼ passive-simulator) (proj₂ second-security)

composed-full : QAvailabilityᴿ.SecureAvailable (¼ ℚ.+ ¼) (¼ ℚ.+ ¼) passive passive realᵒ idealᵒ
composed-full = QAvailabilityᴿ.secure-trans
  {f = realᵒ} {g = middleᵒ} {h = idealᵒ} first-full second-full

native-full : SecurelyConstructs ½ ½ passive passive realᵒ idealᵒ
native-full = Equivalence.to
  (SecureAvailable⇔SecurelyConstructs {f = realᵒ} {g = idealᵒ}) composed-full

no-small-full : ε ℚ.< ½ → ¬ (QAvailabilityᴿ.SecureAvailable ε ½ passive passive realᵒ idealᵒ)
no-small-full small c = no-small-security small (QAvailabilityᴿ.SecureAvailable.security c)
