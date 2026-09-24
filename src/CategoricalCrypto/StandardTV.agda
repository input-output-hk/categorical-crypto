{-# OPTIONS --safe --without-K #-}

-- The standard UC layer instantiated at the vanishing-TV world:
-- 𝒞 = ℐ = 𝒞^ω, ℳ = ⊗, ℰ = ℰᵗᵛ.

open import Level

open import CategoricalCrypto.MachineAxioms

module CategoricalCrypto.StandardTV
  {o ℓ e os ℓs qs : Level} (MA : MachineAxioms o ℓ e os ℓs qs)
  (hom-triv : MachineAxioms.HomTransportTrivial MA)
  where

open import Function

open import CategoricalCrypto.FamilyCategory MA
open import CategoricalCrypto.Standard2
open import CategoricalCrypto.UCSetup

import CategoricalCrypto.VanishingTV as VTV
private module TV = VTV MA

open StdUC 𝒞^ω TV.ℰᵗᵛ public
open TV public using (absorb; _≈ℰ[_]_; VanishingBound)

StdSetupᵗᵛ : UCSetup o (ℓ ⊔ qs) e o (ℓ ⊔ qs) e (o ⊔ ℓ ⊔ qs) (o ⊔ ℓ ⊔ qs)
StdSetupᵗᵛ = StdSetup

grade-stableᵗᵛ : GradeStable
grade-stableᵗᵛ = TV.grade-stable hom-triv

≈ᵁ⇔≈ℰᵗᵛ : {A B X : Channel} {f g : A ⇒ T₀ X B} → f ≈ᵁ g ⇔ f ≈ℰ g
≈ᵁ⇔≈ℰᵗᵛ {f = f} {g} = mk⇔ {B = f ≈ℰ g} ≈ᵁ⇒≈ℰ (bridge grade-stableᵗᵛ)
