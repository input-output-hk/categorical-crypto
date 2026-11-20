{-# OPTIONS --safe --without-K #-}

-- Category laws are simulations of one step: unitors collapse a trivial
-- state factor, and associativity rebrackets the state tree.

open import Categories.Category.Core
open import Categories.Category.EquivClosureHelper
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Subcategory
import Categories.Category.Monoidal.Utilities as MonoidalUtilities
open import Categories.Coherence.Symmetric.Tactic

open import Level

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.Machines.Category
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e) (𝒫 : WideSymmetricMonoidalSubcategory 𝒱) where

open SymmetricMonoidalCategory 𝒱
open Core 𝒱
open HomReasoning
open MonoidalUtilities.Shorthands monoidal
open WideSymmetricMonoidalSubcategory 𝒫
open Sim 𝒱 𝒫

open import Categories.Category.Monoidal.Symmetric.Properties.Ext symmetric
open import Categories.Morphism.Reasoning U

private variable A B C D : Obj
                 f i : Machine A B
                 g : Machine B C
                 h : Machine C D

opaque
  unfolding _∘ᴹ_

  assoc-∘ᴹ : (h ∘ᴹ g) ∘ᴹ f ≲ h ∘ᴹ (g ∘ᴹ f)
  assoc-∘ᴹ {h = h} {g = g} {f = f} =
    sim α⇒ selected-α⇒ (⊛-assoc-point (state h) (state g) (state f)) (solve-smc 𝒱)

  identityˡ-∘ᴹ : idᴹ ∘ᴹ f ≲ f
  identityˡ-∘ᴹ = collapseˡ (refl⟩∘⟨ (onL-id ⟩∘⟨refl ○ identityˡ) ○ onR-collapseˡ)

  identityʳ-∘ᴹ : f ∘ᴹ idᴹ ≲ f
  identityʳ-∘ᴹ = collapseʳ (refl⟩∘⟨ (refl⟩∘⟨ onR-id ○ identityʳ) ○ onL-collapseʳ)

  ∘ᴹ-resp-≲ : f ≲ h → g ≲ i → f ∘ᴹ g ≲ h ∘ᴹ i
  ∘ᴹ-resp-≲ u v = record
    { θ          = θ u ⊗₁ θ v
    ; θ-selected = selected-⊗₁ (θ-selected u) (θ-selected v)
    ; θ-point    = ⊛-∘-point (θ-point u) (θ-point v)
    ; θ-step     = glue′ (onL-sim (θ-step u)) (onR-sim (θ-step v))
    }

Mealy-Category : Category o (o ⊔ ℓ) (o ⊔ ℓ ⊔ e)
Mealy-Category = categoryHelperᵉ record
  { Obj       = Obj
  ; _⇒_       = Machine
  ; _≈_       = _≲_
  ; id        = idᴹ
  ; _∘_       = _∘ᴹ_
  ; assoc     = assoc-∘ᴹ
  ; identityˡ = identityˡ-∘ᴹ
  ; identityʳ = identityʳ-∘ᴹ
  ; ∘-resp-≈  = ∘ᴹ-resp-≲
  }

∘ᴹ-resp-≈ᴹ : f ≈ᴹ h → g ≈ᴹ i → f ∘ᴹ g ≈ᴹ h ∘ᴹ i
∘ᴹ-resp-≈ᴹ = Category.∘-resp-≈ Mealy-Category
