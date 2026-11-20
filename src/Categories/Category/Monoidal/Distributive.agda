{-# OPTIONS --safe --without-K #-}

-- Upstream's `Categories.Category.Distributive` with the cartesian product
-- replaced by the monoidal `⊗`.  Uniqueness of maps out of `X ⊗₀ ⊥` is not a
-- field: binary distributivity implies it (`Properties.⊥-unique`).

open import Categories.Category.Cocartesian
open import Categories.Category.Monoidal.Bundle

import Categories.Morphism as M

open import Level

module Categories.Category.Monoidal.Distributive
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e) where

open SymmetricMonoidalCategory 𝒱
open M U

record MonoidalDistributive : Set (levelOfTerm 𝒱) where
  field
    cocartesian : Cocartesian U

  open Cocartesian cocartesian public

  distributeˡ : ∀ {X A B} → (X ⊗₀ A) + (X ⊗₀ B) ⇒ X ⊗₀ (A + B)
  distributeˡ = [ id ⊗₁ i₁ , id ⊗₁ i₂ ]

  field
    isIsoˡ : ∀ {X A B} → IsIso (distributeˡ {X} {A} {B})

  module distributeˡ {X A B} = IsIso (isIsoˡ {X} {A} {B})

  δ⇐ : ∀ {X A B} → X ⊗₀ (A + B) ⇒ (X ⊗₀ A) + (X ⊗₀ B)
  δ⇐ = distributeˡ.inv
