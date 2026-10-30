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

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Frame as Frame
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Tensor as Tensor

module CategoricalCrypto.Machines.Tensor.Structural
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e)
  (dist : MD.MonoidalDistributive 𝒱) (𝒫 : WideSymmetricMonoidalSubcategory 𝒱) where

open SymmetricMonoidalCategory 𝒱
open BraidedProps.Shorthands braided
open Core 𝒱
open Equiv
open Frame 𝒱
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

private variable A B C D X Y : Obj

⊗ᵉ-pureˡ : (h : C ⇒ D) → idᴹ {A} ⊗ᵉ pureᴹ h ≲ pureᴹ (id +₁ h)
⊗ᵉ-pureˡ h = ≲-trans (mk-cong (tstep-cong (onL-cong (⟺ ⊗.identity)) refl)) (⊗ᵉ-pureᴹ id h)

σᴹ-involutive : σᴹ ∘ᴹ σᴹ {A} {B} ≲ idᴹ
σᴹ-involutive = ≲-trans (pureᴹ-∘ _ _) (≲-trans (pureᴹ-cong +-swap∘+-swap) pureᴹ-id)

private
  ρ-i₁ : id {X} ⊗₁ ⊕.unitorʳ.from {A} ∘ id ⊗₁ i₁ ≈ id
  ρ-i₁ = merge₂ʳ ○ (refl⟩⊗⟨ ⊕.unitorʳ.isoʳ) ○ ⊗.identity

  λ-i₂ : id {X} ⊗₁ ⊕.unitorˡ.from {A} ∘ id ⊗₁ i₂ ≈ id
  λ-i₂ = merge₂ʳ ○ (refl⟩⊗⟨ ⊕.unitorˡ.isoʳ) ○ ⊗.identity

tstep-ρ : {k : X ⊗₀ A ⇒ X ⊗₀ B} {l : X ⊗₀ ⊥ ⇒ X ⊗₀ ⊥}
        → id ⊗₁ ⊕.unitorʳ.from ∘ tstep k l ≈ k ∘ id ⊗₁ ⊕.unitorʳ.from
tstep-ρ = δ-unique (pullʳ tstep-i₁ ○ pullˡ ρ-i₁ ○ identityˡ ○ ⟺ (pullʳ ρ-i₁ ○ identityʳ)) ⊥-unique

tstep-λ : {k : X ⊗₀ ⊥ ⇒ X ⊗₀ ⊥} {l : X ⊗₀ A ⇒ X ⊗₀ B}
        → id ⊗₁ ⊕.unitorˡ.from ∘ tstep k l ≈ l ∘ id ⊗₁ ⊕.unitorˡ.from
tstep-λ = δ-unique ⊥-unique (pullʳ tstep-i₂ ○ pullˡ λ-i₂ ○ identityˡ
                            ○ ⟺ (pullʳ λ-i₂ ○ identityʳ))

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

tstep-swap : {k : X ⊗₀ A ⇒ Y ⊗₀ B} {l : X ⊗₀ C ⇒ Y ⊗₀ D}
           → id ⊗₁ +-swap ∘ tstep k l ≈ tstep l k ∘ id ⊗₁ +-swap
tstep-swap = δ-unique
  (pullʳ tstep-i₁ ○ pullˡ (merge₂ʳ ○ refl⟩⊗⟨ +-swap-i₁)
   ○ ⟺ (pullʳ (merge₂ʳ ○ refl⟩⊗⟨ +-swap-i₁) ○ tstep-i₂))
  (pullʳ tstep-i₂ ○ pullˡ (merge₂ʳ ○ refl⟩⊗⟨ +-swap-i₂)
   ○ ⟺ (pullʳ (merge₂ʳ ○ refl⟩⊗⟨ +-swap-i₂) ○ tstep-i₁))

braiding-commuteᴹ : {f : Machine A B} {g : Machine C D} → σᴹ ∘ᴹ f ⊗ᵉ g ≈ᴹ g ⊗ᵉ f ∘ᴹ σᴹ
braiding-commuteᴹ {f = f} {g} =
    ≲⇒≈ᴹ (pure-∘ˡ +-swap (f ⊗ᵉ g))
  ○ᴹ ≲⇒≈ᴹ (sim σ⇒ selected-σ⇒ point-σ
             (pullˡ whisker-comm ○ assoc
              ○ (refl⟩∘⟨ tstep-sim σ-onL σ-onR) ○ sym-assoc ○ (tstep-swap ⟩∘⟨refl)))
  ○ᴹ ≲⇒≈ᴹ˘ (pure-∘ʳ +-swap (g ⊗ᵉ f))
  where
    point-σ : σ⇒ ∘ point (state f ⊛ state g) ≈ point (state g ⊛ state f)
    point-σ = pullˡ (braiding.⇒.commute _) ○ assoc ○ refl⟩∘⟨ (σ-unit ⟩∘⟨refl ○ identityˡ)
