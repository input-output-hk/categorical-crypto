{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.UC.Model.Coverage where

open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.RandomSystems.FullAbstraction using (dualᵒ; T₁-≈ℰ⇒∼ᴿ)
open import CategoricalCrypto.UC.RandomSystems.Morphism using (≈ᴿ⇒≈ᵁ)

-- The cup at the domain's dual already exposes every strategy, including
-- correlations with the ancillary state; arbitrary target grades are allowed.
dual-prefix⇒≈ᵁ : ∀ {A X B} {f g : A ⇒ T₀ X B}
                 → prefix (dualᵒ A) f ≈ℰ prefix (dualᵒ A) g → f ≈ᵁ g
dual-prefix⇒≈ᵁ {f = f} {g} eq = ≈ᴿ⇒≈ᵁ (T₁-≈ℰ⇒∼ᴿ
  (≈ℰ-trans (≈ℰ-sym (unμ f)) (≈ℰ-trans (≈ℰ-cong-post α⇒ eq) (unμ g))))
  where
  unμ : ∀ {A X B} (h : A ⇒ T₀ X B)
      → (α⇒ ∘ prefix (dualᵒ A) h) ≈ℰ T₁ (dualᵒ A) h
  unμ h = ≈C⇒≈ℰ (𝒞.cancelˡ ℐ.associator.isoʳ)
