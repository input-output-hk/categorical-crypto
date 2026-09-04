{-# OPTIONS --safe --without-K #-}

-- Upstream's `Categories.Category.Distributive` with the cartesian product
-- replaced by the monoidal `⊗`: cocartesian, plus `[ id ⊗₁ i₁ , id ⊗₁ i₂ ]` an
-- iso.  This is much cheaper than a `RigCategory`, because
-- `CocartesianMonoidal`/`CocartesianSymmetricMonoidal` derive `+`-monoidal and
-- `+`-symmetric from `cocartesian` alone — every structural morphism of the
-- coproduct side and all of its coherence is upstream.
--
-- `X ⊗₀ ⊥` being initial is a *consequence* of binary distributivity rather
-- than a field: `[ id , id ] : ⊥ + ⊥ ⇒ ⊥` is invertible because maps out of `⊥`
-- are unique, and `δ⇒` then forces `i₁ ≈ i₂ : X ⊗₀ ⊥ ⇒ (X ⊗₀ ⊥) + (X ⊗₀ ⊥)`.

open import Categories.Category.Cocartesian
open import Categories.Category.Monoidal.Bundle
open import Level using (levelOfTerm)

import Categories.Morphism as M

module Categories.Category.Monoidal.Distributive
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e) where

open SymmetricMonoidalCategory 𝒱
open M U using (IsIso)

record MonoidalDistributive : Set (levelOfTerm 𝒱) where
  field
    cocartesian : Cocartesian U

  open Cocartesian cocartesian public

  distributeˡ : ∀ {X A B} → (X ⊗₀ A) + (X ⊗₀ B) ⇒ X ⊗₀ (A + B)
  distributeˡ = [ id ⊗₁ i₁ , id ⊗₁ i₂ ]

  field
    distributeˡ-isIso : ∀ {X A B} → IsIso (distributeˡ {X} {A} {B})

  module distributeˡ {X A B} = IsIso (distributeˡ-isIso {X} {A} {B})

  δ⇒ : ∀ {X A B} → (X ⊗₀ A) + (X ⊗₀ B) ⇒ X ⊗₀ (A + B)
  δ⇒ = distributeˡ

  δ⇐ : ∀ {X A B} → X ⊗₀ (A + B) ⇒ (X ⊗₀ A) + (X ⊗₀ B)
  δ⇐ = distributeˡ.inv
