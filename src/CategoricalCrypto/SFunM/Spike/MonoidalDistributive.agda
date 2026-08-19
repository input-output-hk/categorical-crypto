{-# OPTIONS --safe --without-K #-}

-- SPIKE: the hypothesis the machine layer's *interface* tensor actually needs.
--
-- `Spike.Mealy` runs over a symmetric monoidal `𝒱` whose `⊗` pairs STATES.  The
-- interface tensor of `CategoricalCrypto.SFunM.Monoidal` is a different
-- structure: `⊎`/`⊥`, i.e. the coproduct, and `_⊗ᵏ_` case-splits a sum sitting
-- under a state pair — the distributor.  So the hypothesis is upstream's
-- `Categories.Category.Distributive` with the cartesian product replaced by the
-- monoidal `⊗`: cocartesian, plus `[ id ⊗₁ i₁ , id ⊗₁ i₂ ]` an iso.
--
-- Two things come for free and are worth naming, because they are what makes
-- this hypothesis cheap rather than a `RigCategory`:
--   * `Cocartesian` already carries `+-monoidal`/`+-symmetric`, so every
--     structural morphism of the interface tensor and all of its coherence is
--     upstream — nothing here has to prove a pentagon or a hexagon;
--   * a map out of a coproduct is determined by its two components, so the
--     ⊕-side laws are case splits, not coherence chains.

open import Categories.Category.Cocartesian using (Cocartesian)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Level using (levelOfTerm)

import Categories.Morphism as M

module CategoricalCrypto.SFunM.Spike.MonoidalDistributive
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e) where

open SymmetricMonoidalCategory 𝒱
open M U using (IsIso)

record MonoidalDistributive : Set (levelOfTerm 𝒱) where
  field
    cocartesian : Cocartesian U

  open Cocartesian cocartesian public

  -- The canonical map, exactly upstream's `distributeˡ` with `×` for `⊗`.
  distributeˡ : ∀ {X A B} → (X ⊗₀ A) + (X ⊗₀ B) ⇒ X ⊗₀ (A + B)
  distributeˡ = [ id ⊗₁ i₁ , id ⊗₁ i₂ ]

  field
    distributeˡ-isIso : ∀ {X A B} → IsIso (distributeˡ {X} {A} {B})

  module distributeˡ {X A B} = IsIso (distributeˡ-isIso {X} {A} {B})

  -- `δ⇐` is what `_⊗ᵏ_` uses: it exposes the sum so the two branches can be
  -- copaired.
  δ⇒ : ∀ {X A B} → (X ⊗₀ A) + (X ⊗₀ B) ⇒ X ⊗₀ (A + B)
  δ⇒ = distributeˡ

  δ⇐ : ∀ {X A B} → X ⊗₀ (A + B) ⇒ (X ⊗₀ A) + (X ⊗₀ B)
  δ⇐ = distributeˡ.inv
