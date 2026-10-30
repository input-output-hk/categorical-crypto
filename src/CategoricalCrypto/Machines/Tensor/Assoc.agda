{-# OPTIONS --safe --without-K #-}

-- Tensor functoriality splits into one-sided actions whose trivial state
-- factors collapse.  Associator naturality rebrackets the three states in a
-- single simulation, using the leaf squares from `Machines.Category`.

open import Categories.Category.Core
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Subcategory
import Categories.Category.Cocartesian.Ext as CE
import Categories.Category.Monoidal.Distributive as MD
import Categories.Category.Monoidal.Distributive.Properties as MDP
import Categories.Category.Monoidal.Utilities as MonoidalUtilities
import Categories.Morphism.Reasoning as MorRe

import CategoricalCrypto.Machines.Category as MCat
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Frame as Frame
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Tensor as Tensor
import CategoricalCrypto.Machines.Tensor.Structural as Structural

module CategoricalCrypto.Machines.Tensor.Assoc
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e)
  (dist : MD.MonoidalDistributive 𝒱) (𝒫 : WideSymmetricMonoidalSubcategory 𝒱) where

open SymmetricMonoidalCategory 𝒱
open Core 𝒱
open Equiv
open Frame 𝒱
open MCat 𝒱 𝒫
open MD.MonoidalDistributive dist
open CE U cocartesian
open MDP 𝒱 dist
open MonoidalUtilities.Shorthands monoidal
open WideSymmetricMonoidalSubcategory 𝒫
open Sim 𝒱 𝒫
open Structural 𝒱 dist 𝒫
open Tensor 𝒱 dist 𝒫

open import Categories.Category.Monoidal.Reassociation monoidal
open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Morphism.Reasoning U

private
  module ℳ = Category Mealy-Category
  module MR = MorRe Mealy-Category

open ℳ.HomReasoning using ()
  renaming (_⟩∘⟨_ to _⟩∘ᴹ⟨_; refl⟩∘⟨_ to reflᴹ⟩∘ᴹ⟨_; _⟩∘⟨refl to _⟩∘ᴹ⟨reflᴹ)

private variable A B C D E F X : Obj

⊗idᵉ-collapse : (f : Machine A B) → f ⊗ᵉ idᴹ {C} ≲ mk (state f) (tstep (step f) id)
⊗idᵉ-collapse f = collapseʳ (tstep-sim onL-collapseʳ (refl⟩∘⟨ onR-id ○ identityʳ ○ ⟺ identityˡ))

id⊗ᵉ-collapse : (g : Machine C D) → idᴹ {A} ⊗ᵉ g ≲ mk (state g) (tstep id (step g))
id⊗ᵉ-collapse g = collapseˡ (tstep-sim (refl⟩∘⟨ onL-id ○ identityʳ ○ ⟺ identityˡ) onR-collapseˡ)

opaque
  unfolding _∘ᴹ_

  ⊗-split : (f : Machine A B) (g : Machine C D) → f ⊗ᵉ g ≈ᴹ f ⊗ᵉ idᴹ ∘ᴹ idᴹ ⊗ᵉ g
  ⊗-split f g = ≲⇒≈ᴹ˘ (sim (ρ⇒ ⊗₁ λ⇒) (selected-⊗₁ selected-ρ⇒ selected-λ⇒) pt-u step-u)
    where
      pt-u : ρ⇒ ⊗₁ λ⇒ ∘ point ((state f ⊛ Iˢ) ⊛ (Iˢ ⊛ state g)) ≈ point (state f ⊛ state g)
      pt-u = ⊛-point₂ (state f ⊛ Iˢ) (state f) (Iˢ ⊛ state g) (state g)
                      (ρ-point (state f)) (λ-point (state g))

      step-u : (ρ⇒ ⊗₁ λ⇒) ⊗₁ id ∘ onL (step (f ⊗ᵉ idᴹ)) ∘ onR (step (idᴹ ⊗ᵉ g))
             ≈ step (f ⊗ᵉ g) ∘ (ρ⇒ ⊗₁ λ⇒) ⊗₁ id
      step-u = refl⟩∘⟨ (onL-tstep ⟩∘⟨ onR-tstep ○ tstep-∘
               ○ tstep-cong (elimʳ (onR-cong onL-id ○ onR-id)) (elimˡ (onL-cong onR-id ○ onL-id)))
             ○ tstep-sim (onL-sim onL-collapseʳ) (onR-sim onR-collapseˡ)

private
  braid-conj : (M : Machine A B) (N : Machine C D) → M ⊗ᵉ N ≈ᴹ σᴹ ∘ᴹ N ⊗ᵉ M ∘ᴹ σᴹ
  braid-conj M N = ≲⇒≈ᴹ˘ identityˡ-∘ᴹ ○ᴹ (≲⇒≈ᴹ˘ σᴹ-involutive ⟩∘ᴹ⟨reflᴹ)
                 ○ᴹ ≲⇒≈ᴹ assoc-∘ᴹ ○ᴹ (reflᴹ⟩∘ᴹ⟨ braiding-commuteᴹ)

⊗-split′ : (f : Machine A B) (g : Machine C D) → f ⊗ᵉ g ≈ᴹ idᴹ ⊗ᵉ g ∘ᴹ f ⊗ᵉ idᴹ
⊗-split′ f g = braid-conj f g
             ○ᴹ (reflᴹ⟩∘ᴹ⟨ ⊗-split g f ⟩∘ᴹ⟨reflᴹ)
             ○ᴹ MR.center⁻¹ braiding-commuteᴹ (⟺ᴹ braiding-commuteᴹ)
             ○ᴹ MR.cancelInner (≲⇒≈ᴹ σᴹ-involutive)

------------------------------------------------------------------------
-- Functoriality

opaque
  unfolding _∘ᴹ_

  ⊗idᵉ-hom : (g : Machine B C) (f : Machine A B) → (g ∘ᴹ f) ⊗ᵉ idᴹ ≈ᴹ g ⊗ᵉ idᴹ ∘ᴹ f ⊗ᵉ idᴹ {D}
  ⊗idᵉ-hom g f = ≲⇒≈ᴹ (⊗idᵉ-collapse (g ∘ᴹ f))
               ○ᴹ ≲⇒≈ᴹ (mk-cong (⟺ (onL-tstep ⟩∘⟨ onR-tstep ○ tstep-∘
                                    ○ tstep-cong refl (onL-id ⟩∘⟨ onR-id ○ identity²))))
               ○ᴹ ⟺ᴹ (≲⇒≈ᴹ (⊗idᵉ-collapse g) ⟩∘ᴹ⟨ ≲⇒≈ᴹ (⊗idᵉ-collapse f))

id⊗ᵉ-hom : (g : Machine C D) (f : Machine B C) → idᴹ ⊗ᵉ (g ∘ᴹ f) ≈ᴹ idᴹ ⊗ᵉ g ∘ᴹ idᴹ {A} ⊗ᵉ f
id⊗ᵉ-hom g f = braid-conj idᴹ (g ∘ᴹ f)
             ○ᴹ (reflᴹ⟩∘ᴹ⟨ ⊗idᵉ-hom g f ⟩∘ᴹ⟨reflᴹ)
             ○ᴹ ⟺ᴹ ((braid-conj idᴹ g ⟩∘ᴹ⟨ braid-conj idᴹ f)
                    ○ᴹ (ℳ.sym-assoc ⟩∘ᴹ⟨reflᴹ)
                    ○ᴹ MR.cancelInner (≲⇒≈ᴹ σᴹ-involutive)
                    ○ᴹ MR.center reflᴹ)

⊗ᵉ-homomorphism : {f′ : Machine B C} {f : Machine A B} {g′ : Machine E F} {g : Machine D E}
                → (f′ ∘ᴹ f) ⊗ᵉ (g′ ∘ᴹ g) ≈ᴹ f′ ⊗ᵉ g′ ∘ᴹ f ⊗ᵉ g
⊗ᵉ-homomorphism {f′ = f′} {f} {g′} {g} =
    ⊗-split (f′ ∘ᴹ f) (g′ ∘ᴹ g)
  ○ᴹ (⊗idᵉ-hom f′ f ⟩∘ᴹ⟨ id⊗ᵉ-hom g′ g)
  ○ᴹ MR.center (⟺ᴹ (⊗-split f g′) ○ᴹ ⊗-split′ f g′)
  ○ᴹ ⟺ᴹ (MR.center reflᴹ)
  ○ᴹ ⟺ᴹ (⊗-split f′ g′ ⟩∘ᴹ⟨ ⊗-split f g)

tstep-α : {k₁ : X ⊗₀ A ⇒ X ⊗₀ B} {k₂ : X ⊗₀ C ⇒ X ⊗₀ D} {k₃ : X ⊗₀ E ⇒ X ⊗₀ F}
        → id ⊗₁ α+⇒ ∘ tstep (tstep k₁ k₂) k₃
        ≈ tstep k₁ (tstep k₂ k₃) ∘ id ⊗₁ α+⇒
tstep-α {X = X} {k₁ = k₁} {k₂} {k₃} =
  δ-unique (δ-unique (fuse ○ brA ○ ⟺ fuse) (fuse ○ brC ○ ⟺ fuse)) brE
  where
    fuse : {T V₁ V₂ W : Obj} {u : X ⊗₀ V₂ ⇒ T} {j : V₁ ⇒ V₂} {j′ : W ⇒ V₁}
         → (u ∘ id ⊗₁ j) ∘ id ⊗₁ j′ ≈ u ∘ id ⊗₁ (j ∘ j′)
    fuse = assoc ○ (refl⟩∘⟨ merge₂ʳ)

    brA : (id ⊗₁ α+⇒ ∘ tstep (tstep k₁ k₂) k₃) ∘ id ⊗₁ (i₁ ∘ i₁)
        ≈ (tstep k₁ (tstep k₂ k₃) ∘ id ⊗₁ α+⇒) ∘ id ⊗₁ (i₁ ∘ i₁)
    brA = assoc
        ○ (refl⟩∘⟨ ((refl⟩∘⟨ ⟺ merge₂ʳ) ○ sym-assoc ○ (tstep-i₁ ⟩∘⟨refl) ○ assoc
                    ○ (refl⟩∘⟨ tstep-i₁) ○ sym-assoc ○ (merge₂ʳ ⟩∘⟨refl)))
        ○ pullˡ (merge₂ʳ ○ refl⟩⊗⟨ α+⇒-i₁i₁)
        ○ ⟺ (assoc ○ (refl⟩∘⟨ (merge₂ʳ ○ refl⟩⊗⟨ α+⇒-i₁i₁)) ○ tstep-i₁)

    brC : (id ⊗₁ α+⇒ ∘ tstep (tstep k₁ k₂) k₃) ∘ id ⊗₁ (i₁ ∘ i₂)
        ≈ (tstep k₁ (tstep k₂ k₃) ∘ id ⊗₁ α+⇒) ∘ id ⊗₁ (i₁ ∘ i₂)
    brC = assoc
        ○ (refl⟩∘⟨ ((refl⟩∘⟨ ⟺ merge₂ʳ) ○ sym-assoc ○ (tstep-i₁ ⟩∘⟨refl) ○ assoc
                    ○ (refl⟩∘⟨ tstep-i₂) ○ sym-assoc ○ (merge₂ʳ ⟩∘⟨refl)))
        ○ pullˡ (merge₂ʳ ○ refl⟩⊗⟨ α+⇒-i₁i₂)
        ○ ⟺ (assoc ○ (refl⟩∘⟨ (merge₂ʳ ○ refl⟩⊗⟨ α+⇒-i₁i₂))
             ○ (refl⟩∘⟨ ⟺ merge₂ʳ) ○ sym-assoc ○ (tstep-i₂ ⟩∘⟨refl) ○ assoc
             ○ (refl⟩∘⟨ tstep-i₁) ○ sym-assoc ○ (merge₂ʳ ⟩∘⟨refl))

    brE : (id ⊗₁ α+⇒ ∘ tstep (tstep k₁ k₂) k₃) ∘ id ⊗₁ i₂
        ≈ (tstep k₁ (tstep k₂ k₃) ∘ id ⊗₁ α+⇒) ∘ id ⊗₁ i₂
    brE = assoc ○ (refl⟩∘⟨ tstep-i₂) ○ pullˡ (merge₂ʳ ○ refl⟩⊗⟨ α+⇒-i₂)
        ○ ⟺ (assoc ○ (refl⟩∘⟨ (merge₂ʳ ○ refl⟩⊗⟨ α+⇒-i₂))
             ○ (refl⟩∘⟨ ⟺ merge₂ʳ) ○ sym-assoc ○ (tstep-i₂ ⟩∘⟨refl) ○ assoc
             ○ (refl⟩∘⟨ tstep-i₂) ○ sym-assoc ○ (merge₂ʳ ⟩∘⟨refl))

assoc-commuteᴹ : {f : Machine A B} {g : Machine C D} {h : Machine E F}
               → α⇒ᴹ ∘ᴹ (f ⊗ᵉ g) ⊗ᵉ h ≈ᴹ f ⊗ᵉ g ⊗ᵉ h ∘ᴹ α⇒ᴹ
assoc-commuteᴹ {f = f} {g} {h} =
    ≲⇒≈ᴹ (pure-∘ˡ α+⇒ ((f ⊗ᵉ g) ⊗ᵉ h))
  ○ᴹ ≲⇒≈ᴹ (sim α⇒ selected-α⇒ (⊛-assoc-point (state f) (state g) (state h))
      (pullˡ whisker-comm ○ assoc
       ○ (refl⟩∘⟨ (refl⟩∘⟨ tstep-cong onL-tstep refl))
       ○ (refl⟩∘⟨ tstep-sim (tstep-sim (onL-α (step f)) (onLR-α (step g)))
                                (onR-α (step h)))
       ○ sym-assoc
       ○ ((tstep-α ○ (tstep-cong refl (⟺ onR-tstep) ⟩∘⟨refl)) ⟩∘⟨refl)))
  ○ᴹ ≲⇒≈ᴹ˘ (pure-∘ʳ α+⇒ (f ⊗ᵉ (g ⊗ᵉ h)))
