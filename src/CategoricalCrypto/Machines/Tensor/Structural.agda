{-# OPTIONS --safe --without-K #-}

-- The interface tensor's unit and braiding coherence.  Every law here is its
-- `+`-monoidal instance conjugated by `pureᴹ`: the structural machines are pure
-- and `pureᴹ` preserves `∘` and `⊗` (`pureᴹ-∘`, `⊗ᵉ-pureᴹ`), so
-- `triangleᴹ`/`pentagonᴹ`/`hexagonᴹ` are one `pureᴹ-cong` each.
--
-- The two naturalities are not: they relate a structural machine to an
-- arbitrary one.  The unitors' hold because `X ⊗₀ ⊥` is initial (`⊥-unique`),
-- so the summand that would carry the other machine cannot fire; the
-- braiding's is the state braiding `σ⇒` exchanging the two state actions
-- (`σ-onL`/`σ-onR`) while `tstep-swap` exchanges the interface summands.

open import Categories.Category.Core
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Pure
open import Categories.Category.Monoidal.Symmetric
import Categories.Category.Cocartesian as Cocart
import Categories.Category.Cocartesian.Ext as CE
import Categories.Category.Monoidal.Braided.Properties as BraidedProps
import Categories.Category.Monoidal.Distributive as MD
import Categories.Category.Monoidal.Distributive.Properties as MDP
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

import CategoricalCrypto.Machines.Category as MCat
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Frame as Frame
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Tensor as Tensor

module CategoricalCrypto.Machines.Tensor.Structural
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e)
  (dist : MD.MonoidalDistributive 𝒱) (𝒫 : PureSub 𝒱) where

open SymmetricMonoidalCategory 𝒱
open BraidedProps.Shorthands braided
open Core 𝒱
open Equiv
open Frame 𝒱
open MCat 𝒱 𝒫
open MD.MonoidalDistributive dist
open CE U cocartesian
open MDP 𝒱 dist
open MonoidalUtilities.Shorthands monoidal
open PureSub 𝒫
open Sim 𝒱 𝒫
open Tensor 𝒱 dist 𝒫

open import Categories.Category.Monoidal.Properties.Ext monoidal
open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Category.Monoidal.Symmetric.Properties.Ext symmetric
open import Categories.Morphism.Reasoning U

private
  module ⊕Sym = Symmetric (Cocart.CocartesianSymmetricMonoidal.+-symmetric U cocartesian)
  module ℳ = Category Mealy-Category

open ℳ.HomReasoning using ()
  renaming (_⟩∘⟨_ to _⟩∘ᴹ⟨_; refl⟩∘⟨_ to reflᴹ⟩∘ᴹ⟨_; _⟩∘⟨refl to _⟩∘ᴹ⟨reflᴹ)

private variable A B C D X Y : Obj

------------------------------------------------------------------------
-- Pure machines under the interface tensor

⊗ᵉ-pureˡ : (h : C ⇒ D) → (idᴹ {A} ⊗ᵉ pureᴹ h) ≲ pureᴹ (id +₁ h)
⊗ᵉ-pureˡ h = ≲-trans (mk-cong (tstep-cong (onL-cong (⟺ ⊗.identity)) refl))
                     (⊗ᵉ-pureᴹ id h)

⊗ᵉ-pureʳ : (h : A ⇒ B) → (pureᴹ h ⊗ᵉ idᴹ {C}) ≲ pureᴹ (h +₁ id)
⊗ᵉ-pureʳ h = ≲-trans (mk-cong (tstep-cong refl (onR-cong (⟺ ⊗.identity))))
                     (⊗ᵉ-pureᴹ h id)

------------------------------------------------------------------------
-- Coherence

pure-iso : {h : A ⇒ B} {h⁻ : B ⇒ A} → h⁻ ∘ h ≈ id → (pureᴹ h⁻ ∘ᴹ pureᴹ h) ≲ idᴹ
pure-iso eq = ≲-trans (pureᴹ-∘ _ _) (≲-trans (pureᴹ-cong eq) pureᴹ-id)

σᴹ-involutive : (σᴹ ∘ᴹ σᴹ {A} {B}) ≲ idᴹ
σᴹ-involutive = pure-iso +-swap∘swap

triangleᴹ : ((idᴹ {A} ⊗ᵉ λ⇒ᴹ {B}) ∘ᴹ α⇒ᴹ) ≈ᴹ (ρ⇒ᴹ ⊗ᵉ idᴹ)
triangleᴹ = (≲⇒≈ᴹ (⊗ᵉ-pureˡ ⊕.unitorˡ.from) ⟩∘ᴹ⟨reflᴹ)
          ○ᴹ ≲⇒≈ᴹ (≲-trans (pureᴹ-∘ _ _) (pureᴹ-cong ⊕.triangle))
          ○ᴹ ≲⇒≈ᴹ˘ (⊗ᵉ-pureʳ ⊕.unitorʳ.from)

pentagonᴹ : ((idᴹ ⊗ᵉ α⇒ᴹ {B} {C} {D}) ∘ᴹ (α⇒ᴹ ∘ᴹ (α⇒ᴹ {A} ⊗ᵉ idᴹ))) ≈ᴹ (α⇒ᴹ ∘ᴹ α⇒ᴹ)
pentagonᴹ = (≲⇒≈ᴹ (⊗ᵉ-pureˡ ⊕.associator.from)
               ⟩∘ᴹ⟨ (reflᴹ⟩∘ᴹ⟨ ≲⇒≈ᴹ (⊗ᵉ-pureʳ ⊕.associator.from)))
          ○ᴹ (reflᴹ⟩∘ᴹ⟨ ≲⇒≈ᴹ (pureᴹ-∘ _ _))
          ○ᴹ ≲⇒≈ᴹ (≲-trans (pureᴹ-∘ _ _) (pureᴹ-cong ⊕.pentagon))
          ○ᴹ ≲⇒≈ᴹ˘ (pureᴹ-∘ _ _)

hexagonᴹ : ((idᴹ ⊗ᵉ σᴹ {A} {C}) ∘ᴹ (α⇒ᴹ ∘ᴹ (σᴹ {A} {B} ⊗ᵉ idᴹ))) ≈ᴹ (α⇒ᴹ ∘ᴹ (σᴹ ∘ᴹ α⇒ᴹ))
hexagonᴹ = (≲⇒≈ᴹ (⊗ᵉ-pureˡ +-swap) ⟩∘ᴹ⟨ (reflᴹ⟩∘ᴹ⟨ ≲⇒≈ᴹ (⊗ᵉ-pureʳ +-swap)))
         ○ᴹ (reflᴹ⟩∘ᴹ⟨ ≲⇒≈ᴹ (pureᴹ-∘ _ _))
         ○ᴹ ≲⇒≈ᴹ (≲-trans (pureᴹ-∘ _ _) (pureᴹ-cong ⊕Sym.hexagon₁))
         ○ᴹ ≲⇒≈ᴹ˘ (pureᴹ-∘ _ _)
         ○ᴹ (reflᴹ⟩∘ᴹ⟨ ≲⇒≈ᴹ˘ (pureᴹ-∘ _ _))

------------------------------------------------------------------------
-- Unitor naturality

private
  ρ-i₁ : id {X} ⊗₁ ⊕.unitorʳ.from {A} ∘ id ⊗₁ i₁ ≈ id
  ρ-i₁ = merge₂ʳ ○ (refl⟩⊗⟨ ⊕.unitorʳ.isoʳ) ○ ⊗.identity

  λ-i₂ : id {X} ⊗₁ ⊕.unitorˡ.from {A} ∘ id ⊗₁ i₂ ≈ id
  λ-i₂ = merge₂ʳ ○ (refl⟩⊗⟨ ⊕.unitorˡ.isoʳ) ○ ⊗.identity

tstep-ρ : {k : X ⊗₀ A ⇒ X ⊗₀ B} {l : X ⊗₀ ⊥ ⇒ X ⊗₀ ⊥}
        → id ⊗₁ ⊕.unitorʳ.from ∘ tstep k l ≈ k ∘ id ⊗₁ ⊕.unitorʳ.from
tstep-ρ = δ-unique (pullʳ tstep-i₁ ○ pullˡ ρ-i₁ ○ identityˡ
                    ○ ⟺ (pullʳ ρ-i₁ ○ identityʳ)) ⊥-unique

tstep-λ : {k : X ⊗₀ ⊥ ⇒ X ⊗₀ ⊥} {l : X ⊗₀ A ⇒ X ⊗₀ B}
        → id ⊗₁ ⊕.unitorˡ.from ∘ tstep k l ≈ l ∘ id ⊗₁ ⊕.unitorˡ.from
tstep-λ = δ-unique ⊥-unique
                   (pullʳ tstep-i₂ ○ pullˡ λ-i₂ ○ identityˡ
                    ○ ⟺ (pullʳ λ-i₂ ○ identityʳ))

unitorˡ-commuteᴹ : {f : Machine A B} → (λ⇒ᴹ ∘ᴹ (idᴹ ⊗ᵉ f)) ≈ᴹ (f ∘ᴹ λ⇒ᴹ)
unitorˡ-commuteᴹ {f = f} =
    ≲⇒≈ᴹ (pure-∘ˡ ⊕.unitorˡ.from (idᴹ ⊗ᵉ f))
  ○ᴹ ≲⇒≈ᴹ (collapseˡ ((refl⟩∘⟨ tstep-λ) ○ pullˡ onR-collapseˡ ○ assoc
                      ○ (refl⟩∘⟨ ⟺ (pad-transport λ⇒ ⊕.unitorˡ.from)) ○ sym-assoc))
  ○ᴹ ≲⇒≈ᴹ˘ (pure-∘ʳ ⊕.unitorˡ.from f)

unitorʳ-commuteᴹ : {f : Machine A B} → (ρ⇒ᴹ ∘ᴹ (f ⊗ᵉ idᴹ)) ≈ᴹ (f ∘ᴹ ρ⇒ᴹ)
unitorʳ-commuteᴹ {f = f} =
    ≲⇒≈ᴹ (pure-∘ˡ ⊕.unitorʳ.from (f ⊗ᵉ idᴹ))
  ○ᴹ ≲⇒≈ᴹ (collapseʳ ((refl⟩∘⟨ tstep-ρ) ○ pullˡ onL-collapseʳ ○ assoc
                      ○ (refl⟩∘⟨ ⟺ (pad-transport ρ⇒ ⊕.unitorʳ.from)) ○ sym-assoc))
  ○ᴹ ≲⇒≈ᴹ˘ (pure-∘ʳ ⊕.unitorʳ.from f)

------------------------------------------------------------------------
-- Braiding naturality

tstep-swap : {k : X ⊗₀ A ⇒ Y ⊗₀ B} {l : X ⊗₀ C ⇒ Y ⊗₀ D}
           → id ⊗₁ +-swap ∘ tstep k l ≈ tstep l k ∘ id ⊗₁ +-swap
tstep-swap = δ-unique
  (pullʳ tstep-i₁ ○ pullˡ (merge₂ʳ ○ refl⟩⊗⟨ +-swap-i₁)
   ○ ⟺ (pullʳ (merge₂ʳ ○ refl⟩⊗⟨ +-swap-i₁) ○ tstep-i₂))
  (pullʳ tstep-i₂ ○ pullˡ (merge₂ʳ ○ refl⟩⊗⟨ +-swap-i₂)
   ○ ⟺ (pullʳ (merge₂ʳ ○ refl⟩⊗⟨ +-swap-i₂) ○ tstep-i₁))

braiding-commuteᴹ : {f : Machine A B} {g : Machine C D}
                  → (σᴹ ∘ᴹ (f ⊗ᵉ g)) ≈ᴹ ((g ⊗ᵉ f) ∘ᴹ σᴹ)
braiding-commuteᴹ {f = f} {g} =
    ≲⇒≈ᴹ (pure-∘ˡ +-swap (f ⊗ᵉ g))
  ○ᴹ ≲⇒≈ᴹ (sim σ⇒ pure-σ⇒ point-σ
             (pullˡ (⟺ (pad-transport σ⇒ +-swap)) ○ assoc
              ○ (refl⟩∘⟨ tstep-sim σ-onL σ-onR) ○ sym-assoc ○ (tstep-swap ⟩∘⟨refl)))
  ○ᴹ ≲⇒≈ᴹ˘ (pure-∘ʳ +-swap (g ⊗ᵉ f))
  where
    point-σ : σ⇒ ∘ point (state f ⊛ state g) ≈ point (state g ⊛ state f)
    point-σ = pullˡ (braiding.⇒.commute _) ○ assoc
            ○ (refl⟩∘⟨ (σ-unit ⟩∘⟨refl ○ identityˡ))
