{-# OPTIONS --safe --without-K #-}

-- Associativity of the tensor product of machines

open import Categories.Category.Core
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Subcategory
import Categories.Category.Monoidal.Distributive as MD
import Categories.Category.Monoidal.Distributive.Context as MDC
import Categories.Category.Monoidal.Distributive.Properties as MDP
import Categories.Category.Monoidal.Utilities as MonoidalUtilities
import Categories.Morphism.Reasoning as MorRe

import CategoricalCrypto.Machines.Category as MCat
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Tensor as Tensor
import CategoricalCrypto.Machines.Tensor.Structural as Structural

module CategoricalCrypto.Machines.Tensor.Assoc
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e)
  (dist : MD.MonoidalDistributive 𝒱) (𝒫 : WideSymmetricMonoidalSubcategory 𝒱) where

open SymmetricMonoidalCategory 𝒱
open Core 𝒱
open Equiv
open MCat 𝒱 𝒫
open MD.MonoidalDistributive dist
open MDP 𝒱 dist
open MonoidalUtilities.Shorthands monoidal
open WideSymmetricMonoidalSubcategory 𝒫
open Sim 𝒱 𝒫
open Structural 𝒱 dist 𝒫
open Tensor 𝒱 dist 𝒫

open import Categories.Category.Monoidal.Reassociation monoidal
open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Category.Monoidal.Symmetric.Properties.Ext symmetric
open import Categories.Morphism.Reasoning U

private
  module ℳ = Category Mealy-Category
  module MR = MorRe Mealy-Category

open ℳ.HomReasoning using ()
  renaming (_⟩∘⟨_ to _⟩∘ᴹ⟨_; refl⟩∘⟨_ to reflᴹ⟩∘ᴹ⟨_; _⟩∘⟨refl to _⟩∘ᴹ⟨reflᴹ)

private variable A B C D E F : Obj

opaque
  unfolding _∘ᴹ_

  ⊗-split : (f : Machine A B) (g : Machine C D) → f ⊗ᵉ g ≈ᴹ f ⊗ᵉ idᴹ ∘ᴹ idᴹ ⊗ᵉ g
  ⊗-split f g = ≲⇒≈ᴹ˘ (≲-trans (∘ᴹ-resp-≲ (⊗idᵉ-collapse f) (id⊗ᵉ-collapse g))
    (mk-cong (onL-tstep ⟩∘⟨ onR-tstep ○ tstep-∘
      ○ tstep-cong (elimʳ onR-id) (elimˡ onL-id))))

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
  id⊗ᵉ-hom g f = ≲⇒≈ᴹ (id⊗ᵉ-collapse (g ∘ᴹ f))
    ○ᴹ ≲⇒≈ᴹ (mk-cong (⟺ (onL-tstep ⟩∘⟨ onR-tstep ○ tstep-∘ ○ tstep-cong (onL-id ⟩∘⟨ onR-id ○ identity²) refl)))
    ○ᴹ ⟺ᴹ (≲⇒≈ᴹ (id⊗ᵉ-collapse g) ⟩∘ᴹ⟨ ≲⇒≈ᴹ (id⊗ᵉ-collapse f))

⊗ᵉ-homomorphism : {f′ : Machine B C} {f : Machine A B} {g′ : Machine E F} {g : Machine D E}
                → (f′ ∘ᴹ f) ⊗ᵉ (g′ ∘ᴹ g) ≈ᴹ f′ ⊗ᵉ g′ ∘ᴹ f ⊗ᵉ g
⊗ᵉ-homomorphism {f′ = f′} {f} {g′} {g} =
    ⊗-split (f′ ∘ᴹ f) (g′ ∘ᴹ g)
  ○ᴹ (⊗idᵉ-hom f′ f ⟩∘ᴹ⟨ id⊗ᵉ-hom g′ g)
  ○ᴹ MR.center (⟺ᴹ (⊗-split f g′) ○ᴹ ⊗-split′ f g′)
  ○ᴹ ⟺ᴹ (MR.center reflᴹ)
  ○ᴹ ⟺ᴹ (⊗-split f′ g′ ⟩∘ᴹ⟨ ⊗-split f g)

assoc-commuteᴹ : {f : Machine A B} {g : Machine C D} {h : Machine E F}
               → α⇒ᴹ ∘ᴹ (f ⊗ᵉ g) ⊗ᵉ h ≈ᴹ f ⊗ᵉ g ⊗ᵉ h ∘ᴹ α⇒ᴹ
assoc-commuteᴹ {f = f} {g} {h} =
    ≲⇒≈ᴹ (pure-∘ˡ +-assocˡ ((f ⊗ᵉ g) ⊗ᵉ h))
  ○ᴹ ≲⇒≈ᴹ (sim α⇒ selected-α⇒ (⊛-assoc-point (state f) (state g) (state h))
      (pullˡ whisker-comm ○ assoc
       ○ refl⟩∘⟨ refl⟩∘⟨ tstep-cong onL-tstep refl
       ○ refl⟩∘⟨ tstep-sim (tstep-sim (onL-α (step f)) (onLR-α (step g))) (onR-α (step h))
       ○ sym-assoc
       ○ (MDC.tstep-α 𝒱 dist _ ○ tstep-cong refl (⟺ onR-tstep) ⟩∘⟨refl) ⟩∘⟨refl))
  ○ᴹ ≲⇒≈ᴹ˘ (pure-∘ʳ +-assocˡ (f ⊗ᵉ g ⊗ᵉ h))
