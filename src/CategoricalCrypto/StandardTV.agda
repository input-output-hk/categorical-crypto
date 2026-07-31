{-# OPTIONS --safe --without-K #-}

-- The standard UC layer instantiated at the vanishing-TV world:
-- 𝒞 = ℐ = 𝒞^ω, ℳ = ⊗, ℰ = ℰᵗᵛ.

open import Axiom.UniquenessOfIdentityProofs using (UIP)
open import Level

open import Categories.Category.Monoidal

open import CategoricalCrypto.MachineAxioms

module CategoricalCrypto.StandardTV
  {o ℓ e os ℓs qs : Level} (MA : MachineAxioms o ℓ e os ℓs qs)
  (Obj-set : UIP (MonoidalCategory.Obj (MachineAxioms.𝕄 MA)))
  where

open import Data.Nat using (ℕ)
open import Function

open import CategoricalCrypto.FamilyCategory MA
open import CategoricalCrypto.Standard2
open import CategoricalCrypto.UCSetup

open import Categories.Functor.Monoidal.CurriedTensor.Properties 𝒞^ω using (T₁-⊗)

import CategoricalCrypto.VanishingTV as VTV
private module TV = VTV MA

open StdUC 𝒞^ω TV.ℰᵗᵛ public
open TV public using () renaming
  ( absorb to absorbᵗᵛ; _≈ℰ[_]_ to infix 4 _≈ℰᵗᵛ[_]_
  ; VanishingBound to VanishingBoundᵗᵛ )

StdSetupᵗᵛ : UCSetup o (ℓ ⊔ qs) e o (ℓ ⊔ qs) e (o ⊔ ℓ ⊔ qs) (o ⊔ ℓ ⊔ qs)
StdSetupᵗᵛ = StdSetup

grade-stableᵗᵛ : GradeStable
grade-stableᵗᵛ Y {h} {h′} e =
  ≈ℰ-trans (≈C⇒≈ℰ (T₁-⊗ Y h))
    (≈ℰ-trans (TV.grade-stable Obj-set Y e) (≈ℰ-sym (≈C⇒≈ℰ (T₁-⊗ Y h′))))

≈ᵁ⇔≈ℰᵗᵛ : {A B X : Channel} {f g : A ⇒ T₀ X B} → f ≈ᵁ g ⇔ f ≈ℰ g
≈ᵁ⇔≈ℰᵗᵛ {A} {B} {X} {f} {g} =
  mk⇔ (≈ᵁ⇒≈ℰ {A = A} {X = X} {B = B} {f = f} {g = g})
      (bridge {A = A} {X = X} {B = B} {f = f} {g = g} grade-stableᵗᵛ)
