{-# OPTIONS --safe --without-K #-}

-- A wide symmetric monoidal subcategory of `𝒱`, presented as a predicate on
-- morphisms: the structural isos are inside it, and `id`, `_∘_` and `_⊗₁_` keep
-- one inside.
--
-- Iteration over a Kleisli base is uniform along the *pure* (`return`-composed)
-- morphisms only — an arbitrary Kleisli map is effectful, and transferring a
-- loop along one would duplicate its effect — so a layer that spends uniformity
-- has to say which morphisms it spends it at.  That is what this predicate is:
-- the machine layer's simulations and its iteration hypothesis are both stated
-- along `Pure`.
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
open Equiv
open MonoidalUtilities.Shorthands monoidal

private variable A B C D : Obj

record PureSub : Set (o ⊔ suc (ℓ ⊔ e)) where
  field
    Pure : {A B : Obj} → A ⇒ B → Set (ℓ ⊔ e)

    pure-resp-≈ : {f g : A ⇒ B} → f ≈ g → Pure f → Pure g
    pure-id : Pure (id {A})
    pure-∘  : {f : B ⇒ C} {g : A ⇒ B} → Pure f → Pure g → Pure (f ∘ g)
    pure-⊗₁ : {f : A ⇒ B} {g : C ⇒ D} → Pure f → Pure g → Pure (f ⊗₁ g)
    pure-λ⇒ : Pure (λ⇒ {A})
    pure-ρ⇒ : Pure (ρ⇒ {A})
    pure-α⇒ : Pure (α⇒ {A} {B} {C})
    pure-σ⇒ : Pure (σ⇒ {A} {B})
