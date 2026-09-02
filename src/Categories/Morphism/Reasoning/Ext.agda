{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Extensions to `Categories.Morphism.Reasoning`.
------------------------------------------------------------------------

open import Categories.Category.Core

module Categories.Morphism.Reasoning.Ext {o ℓ e} (𝒞 : Category o ℓ e) where

open Category 𝒞
open HomReasoning
open import Categories.Morphism.Reasoning.Core 𝒞

inv-resp : ∀ {A B} {f g : A ⇒ B} {fi gi : B ⇒ A}
         → fi ∘ f ≈ id → g ∘ gi ≈ id → f ≈ g → fi ≈ gi
inv-resp fif ggi f≈g = introʳ ggi ○ (refl⟩∘⟨ ((⟺ f≈g) ⟩∘⟨refl)) ○ cancelˡ fif
