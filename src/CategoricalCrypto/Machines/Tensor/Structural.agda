{-# OPTIONS --safe --without-K #-}

-- Naturality uses the arbitrary machine's state. Unitor naturality uses
-- initiality of `X ⊗₀ ⊥`; braiding naturality exchanges both state actions
-- and interface summands.

open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Subcategory
import Categories.Category.Cocartesian.Ext as CE
import Categories.Category.Monoidal.Braided.Properties as BraidedProps
import Categories.Category.Monoidal.Distributive as MD
import Categories.Category.Monoidal.Distributive.Properties as MDP
import Categories.Category.Monoidal.Utilities as MonoidalUtilities
open import Categories.Coherence.Symmetric.Tactic

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Tensor as Tensor

module CategoricalCrypto.Machines.Tensor.Structural
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e)
  (dist : MD.MonoidalDistributive 𝒱) (𝒫 : WideSymmetricMonoidalSubcategory 𝒱) where

open SymmetricMonoidalCategory 𝒱
open BraidedProps.Shorthands braided
open Core 𝒱
open Equiv
open MD.MonoidalDistributive dist
open CE U cocartesian
open MDP 𝒱 dist
open MonoidalUtilities.Shorthands monoidal
open WideSymmetricMonoidalSubcategory 𝒫
open Sim 𝒱 𝒫
open Tensor 𝒱 dist 𝒫

open import Categories.Category.Monoidal.Reassociation monoidal
open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Category.Monoidal.Symmetric.Properties.Ext symmetric
open import Categories.Morphism.Reasoning U

private variable A B C D : Obj

⊗ᵉ-pureˡ : (h : C ⇒ D) → idᴹ {A} ⊗ᵉ pureᴹ h ≲ pureᴹ (id +₁ h)
⊗ᵉ-pureˡ h = ≲-trans (mk-cong (tstep-cong (onL-cong (⟺ ⊗.identity)) refl)) (⊗ᵉ-pureᴹ id h)

σᴹ-involutive : σᴹ ∘ᴹ σᴹ {A} {B} ≲ idᴹ
σᴹ-involutive = ≲-trans (pureᴹ-∘ _ _) (≲-trans (pureᴹ-cong +-swap∘+-swap) pureᴹ-id)

unitorˡ-commuteᴹ : {f : Machine A B} → λ⇒ᴹ ∘ᴹ idᴹ ⊗ᵉ f ≈ᴹ f ∘ᴹ λ⇒ᴹ
unitorˡ-commuteᴹ {f = f} =
    ≲⇒≈ᴹ (pure-∘ˡ ⊕.unitorˡ.from (idᴹ ⊗ᵉ f))
  ○ᴹ ≲⇒≈ᴹ (collapseˡ ((refl⟩∘⟨ tstep-λ) ○ pullˡ onR-collapseˡ ○ assoc
                      ○ (refl⟩∘⟨ whisker-comm) ○ sym-assoc))
  ○ᴹ ≲⇒≈ᴹ˘ (pure-∘ʳ ⊕.unitorˡ.from f)

unitorʳ-commuteᴹ : {f : Machine A B} → ρ⇒ᴹ ∘ᴹ f ⊗ᵉ idᴹ ≈ᴹ f ∘ᴹ ρ⇒ᴹ
unitorʳ-commuteᴹ {f = f} =
    ≲⇒≈ᴹ (pure-∘ˡ ⊕.unitorʳ.from (f ⊗ᵉ idᴹ))
  ○ᴹ ≲⇒≈ᴹ (collapseʳ ((refl⟩∘⟨ tstep-ρ) ○ pullˡ onL-collapseʳ ○ assoc
                      ○ (refl⟩∘⟨ whisker-comm) ○ sym-assoc))
  ○ᴹ ≲⇒≈ᴹ˘ (pure-∘ʳ ⊕.unitorʳ.from f)

braiding-commuteᴹ : {f : Machine A B} {g : Machine C D} → σᴹ ∘ᴹ f ⊗ᵉ g ≈ᴹ g ⊗ᵉ f ∘ᴹ σᴹ
braiding-commuteᴹ {f = f} {g} =
    ≲⇒≈ᴹ (pure-∘ˡ +-swap (f ⊗ᵉ g))
  ○ᴹ ≲⇒≈ᴹ (sim σ⇒ selected-σ⇒ (⊛-swap-point (state f) (state g))
             (pullˡ whisker-comm ○ assoc
              ○ (refl⟩∘⟨ tstep-sim σ-onL σ-onR) ○ sym-assoc ○ (tstep-swap ⟩∘⟨refl)))
  ○ᴹ ≲⇒≈ᴹ˘ (pure-∘ʳ +-swap (g ⊗ᵉ f))
