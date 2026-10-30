{-# OPTIONS --safe --without-K #-}

-- A wide symmetric monoidal subcategory of `𝒱`, presented as a predicate on
-- morphisms closed under `_∘_` and `_⊗₁_` and containing `id` and the structural
-- isomorphisms in both directions (`σ⇒` is its own inverse).
-- Iteration over a Kleisli base is uniform only along the pure
-- (`return`-composed) morphisms: transferring a loop along an effectful map
-- would duplicate its effect.
--
-- The predicate's level is `ℓ ⊔ e`, not a parameter: the intended instance's
-- purity (`∃ h. f ≈ pure h` at `Kl(Dₚ)`) lands there, and a level parameter
-- would propagate into every hom-set level of the layer.

open import Categories.Category.Monoidal.Bundle
import Categories.Category.Monoidal.Braided.Properties as BraidedProps
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

open import Level

module Categories.Category.Monoidal.Pure
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e) where

open SymmetricMonoidalCategory 𝒱
open BraidedProps.Shorthands braided
open MonoidalUtilities.Shorthands monoidal

private variable A B C D : Obj

record PureSub : Set (o ⊔ suc (ℓ ⊔ e)) where
  field
    Pure : A ⇒ B → Set (ℓ ⊔ e)

    pure-resp-≈ : {f g : A ⇒ B} → f ≈ g → Pure f → Pure g
    pure-id : Pure (id {A})
    pure-∘  : {f : B ⇒ C} {g : A ⇒ B} → Pure f → Pure g → Pure (f ∘ g)
    pure-⊗₁ : {f : A ⇒ B} {g : C ⇒ D} → Pure f → Pure g → Pure (f ⊗₁ g)
    pure-λ⇒ : Pure (λ⇒ {A})
    pure-λ⇐ : Pure (λ⇐ {A})
    pure-ρ⇒ : Pure (ρ⇒ {A})
    pure-ρ⇐ : Pure (ρ⇐ {A})
    pure-α⇒ : Pure (α⇒ {A} {B} {C})
    pure-α⇐ : Pure (α⇐ {A} {B} {C})
    pure-σ⇒ : Pure (σ⇒ {A} {B})
