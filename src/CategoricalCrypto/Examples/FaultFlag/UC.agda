{-# OPTIONS --safe --without-K --guardedness #-}

-- SECURITY-ONLY construction in QSetupᴿ, not its independent availability
-- condition.  Both quarter-error steps are proved from the finite initial laws;
-- neither is a weakening of a zero-error theorem.  See the RS plan §4.6.

open import Categories.Category
open import Categories.Category.Monoidal.Bundle

open import Data.Bool.Base
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ; ½)
open import Data.Rational.Properties
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Negation

open import ProbabilisticLogic.Dp

open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.Examples.FaultFlag
open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Model.Graded
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.RandomSystems.Advantage
open import CategoricalCrypto.UC.RandomSystems.Composition
open import CategoricalCrypto.UC.RandomSystems.Construction
open import CategoricalCrypto.UC.RandomSystems.Quantitative

import CategoricalCrypto.UC.Model.Setup as PM

module CategoricalCrypto.Examples.FaultFlag.UC where

private
  module G = MonoidalCategory 𝔾ᵒ
  module P = Category 𝒫ᴵ
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
