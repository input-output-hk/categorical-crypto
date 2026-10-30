{-# OPTIONS --safe --without-K #-}

-- A wide symmetric monoidal subcategory of `𝒱`, presented as a predicate on
-- morphisms closed under `_∘_` and `_⊗₁_`.

open import Categories.Category.Monoidal.Bundle
import Categories.Category.Monoidal.Braided.Properties as BraidedProps
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

open import Level

module Categories.Category.Monoidal.Subcategory
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e) where

open SymmetricMonoidalCategory 𝒱
open BraidedProps.Shorthands braided
open MonoidalUtilities.Shorthands monoidal

private variable A B C D : Obj

record WideSymmetricMonoidalSubcategory : Set (o ⊔ suc (ℓ ⊔ e)) where
  field
    Selected : A ⇒ B → Set (ℓ ⊔ e)

    selected-resp-≈ : {f g : A ⇒ B} → f ≈ g → Selected f → Selected g
    selected-id : Selected (id {A})
    selected-∘  : {f : B ⇒ C} {g : A ⇒ B} → Selected f → Selected g → Selected (f ∘ g)
    selected-⊗₁ : {f : A ⇒ B} {g : C ⇒ D} → Selected f → Selected g → Selected (f ⊗₁ g)
    selected-λ⇒ : Selected (λ⇒ {A})
    selected-λ⇐ : Selected (λ⇐ {A})
    selected-ρ⇒ : Selected (ρ⇒ {A})
    selected-ρ⇐ : Selected (ρ⇐ {A})
    selected-α⇒ : Selected (α⇒ {A} {B} {C})
    selected-α⇐ : Selected (α⇐ {A} {B} {C})
    selected-σ⇒ : Selected (σ⇒ {A} {B})
