{-# OPTIONS --safe --without-K #-}

-- The interface tensor's functoriality and associator naturality — the two laws
-- that look like they need a re-bracketed state tree's factor recognized as a
-- factor of another tree.  They do not, and `⊗-split` is why: the tensor is the
-- composite of its two one-sided halves, whose trivial state factor collapses
-- away (`⊗idᵉ-collapse`), so each half's homomorphism leaves the state pair
-- alone and the associator's naturality only has to hold one generator at a
-- time.  What is left is ⊕-side, namely `tstep-α`.

open import Categories.Category.Core
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Pure
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
  (dist : MD.MonoidalDistributive 𝒱) (𝒫 : PureSub 𝒱) where

open SymmetricMonoidalCategory 𝒱
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
open Structural 𝒱 dist 𝒫
open Tensor 𝒱 dist 𝒫

open import Categories.Category.Monoidal.Properties monoidal
open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Morphism.Reasoning U

private
  module ℳ = Category Mealy-Category
  module MR = MorRe Mealy-Category

open ℳ.HomReasoning using ()
  renaming (_⟩∘⟨_ to _⟩∘ᴹ⟨_; refl⟩∘⟨_ to reflᴹ⟩∘ᴹ⟨_; _⟩∘⟨refl to _⟩∘ᴹ⟨reflᴹ)

private variable A B C D E F X : Obj

------------------------------------------------------------------------
-- Splitting the tensor into its two one-sided halves

-- The only place a *state* interchange is needed: both sides pair the same two
-- states, up to the two unitors that the one-sided halves' trivial factors
-- contribute.
opaque
  unfolding _∘ᴹ_

  ⊗-split : (f : Machine A B) (g : Machine C D)
          → (f ⊗ᵉ g) ≈ᴹ ((f ⊗ᵉ idᴹ {D}) ∘ᴹ (idᴹ {A} ⊗ᵉ g))
  ⊗-split {A} {B} {C} {D} f g =
    ≲⇒≈ᴹ˘ (sim (ρ⇒ ⊗₁ λ⇒) (pure-⊗₁ pure-ρ⇒ pure-λ⇒) dsc-u pt-u step-u)
    where
      dsc-u : discard (state f ⊛ state g) ∘ (ρ⇒ ⊗₁ λ⇒)
            ≈ discard ((state f ⊛ Iˢ) ⊛ (Iˢ ⊛ state g))
      dsc-u = assoc ○ (refl⟩∘⟨ ⟺ ⊗.homomorphism)
            ○ (refl⟩∘⟨ (ρ-discard (state f) ⟩⊗⟨ λ-discard (state g)))

      pt-u : (ρ⇒ ⊗₁ λ⇒) ∘ point ((state f ⊛ Iˢ) ⊛ (Iˢ ⊛ state g)) ≈ point (state f ⊛ state g)
      pt-u = ⊛-point₂ (state f ⊛ Iˢ) (state f) (Iˢ ⊛ state g) (state g)
                      (ρ-point (state f)) (λ-point (state g))

      step-u : (ρ⇒ ⊗₁ λ⇒) ⊗₁ id ∘ (onL (step (f ⊗ᵉ idᴹ {D})) ∘ onR (step (idᴹ {A} ⊗ᵉ g)))
             ≈ step (f ⊗ᵉ g) ∘ (ρ⇒ ⊗₁ λ⇒) ⊗₁ id
      step-u = (refl⟩∘⟨ ((onL-tstep ⟩∘⟨ onR-tstep) ○ tstep-∘
                         ○ tstep-cong (elimʳ (onR-cong onL-id ○ onR-id))
                                      (elimˡ (onL-cong onR-id ○ onL-id))))
             ○ tstep-sim (onL-sim onL-collapseʳ) (onR-sim onR-collapseˡ)

private
  -- Tensoring on the left is tensoring on the right, conjugated by the braiding.
  braid-conj : (M : Machine A B) (N : Machine C D) → (M ⊗ᵉ N) ≈ᴹ (σᴹ ∘ᴹ ((N ⊗ᵉ M) ∘ᴹ σᴹ))
  braid-conj M N = ≲⇒≈ᴹ˘ identityˡ-∘ᴹ ○ᴹ (≲⇒≈ᴹ˘ σᴹ-involutive ⟩∘ᴹ⟨reflᴹ)
                 ○ᴹ ≲⇒≈ᴹ assoc-∘ᴹ ○ᴹ (reflᴹ⟩∘ᴹ⟨ braiding-commuteᴹ)

-- …so the tensor splits the other way round too, and the two splittings say
-- that the two one-sided halves commute.
⊗-split′ : (f : Machine A B) (g : Machine C D)
         → (f ⊗ᵉ g) ≈ᴹ ((idᴹ {B} ⊗ᵉ g) ∘ᴹ (f ⊗ᵉ idᴹ {C}))
⊗-split′ f g = braid-conj f g
             ○ᴹ (reflᴹ⟩∘ᴹ⟨ (⊗-split g f ⟩∘ᴹ⟨reflᴹ))
             ○ᴹ MR.center⁻¹ braiding-commuteᴹ (⟺ᴹ braiding-commuteᴹ)
             ○ᴹ MR.cancelInner (≲⇒≈ᴹ σᴹ-involutive)

------------------------------------------------------------------------
-- Functoriality

-- A one-sided homomorphism never re-brackets a state tree: both sides pair the
-- same two states, and `tstep-∘` does the rest.
opaque
  unfolding _∘ᴹ_

  ⊗idᵉ-hom : (g : Machine B C) (f : Machine A B)
           → ((g ∘ᴹ f) ⊗ᵉ idᴹ {D}) ≈ᴹ ((g ⊗ᵉ idᴹ {D}) ∘ᴹ (f ⊗ᵉ idᴹ {D}))
  ⊗idᵉ-hom g f = ≲⇒≈ᴹ (⊗idᵉ-collapse (g ∘ᴹ f))
               ○ᴹ ≲⇒≈ᴹ (mk-cong (⟺ ((onL-tstep ⟩∘⟨ onR-tstep) ○ tstep-∘
                                    ○ tstep-cong refl ((onL-id ⟩∘⟨ onR-id) ○ identity²))))
               ○ᴹ ⟺ᴹ (∘ᴹ-resp-≈ᴹ (≲⇒≈ᴹ (⊗idᵉ-collapse g)) (≲⇒≈ᴹ (⊗idᵉ-collapse f)))

id⊗ᵉ-hom : (g : Machine C D) (f : Machine B C)
         → (idᴹ {A} ⊗ᵉ (g ∘ᴹ f)) ≈ᴹ ((idᴹ {A} ⊗ᵉ g) ∘ᴹ (idᴹ {A} ⊗ᵉ f))
id⊗ᵉ-hom g f = braid-conj idᴹ (g ∘ᴹ f)
             ○ᴹ (reflᴹ⟩∘ᴹ⟨ (⊗idᵉ-hom g f ⟩∘ᴹ⟨reflᴹ))
             ○ᴹ ⟺ᴹ ((braid-conj idᴹ g ⟩∘ᴹ⟨ braid-conj idᴹ f)
                    ○ᴹ (ℳ.sym-assoc ⟩∘ᴹ⟨reflᴹ)
                    ○ᴹ MR.cancelInner (≲⇒≈ᴹ σᴹ-involutive)
                    ○ᴹ MR.center reflᴹ)

⊗ᵉ-homomorphism : {f′ : Machine B C} {f : Machine A B} {g′ : Machine E F} {g : Machine D E}
                → ((f′ ∘ᴹ f) ⊗ᵉ (g′ ∘ᴹ g)) ≈ᴹ ((f′ ⊗ᵉ g′) ∘ᴹ (f ⊗ᵉ g))
⊗ᵉ-homomorphism {f′ = f′} {f} {g′} {g} =
    ⊗-split (f′ ∘ᴹ f) (g′ ∘ᴹ g)
  ○ᴹ (⊗idᵉ-hom f′ f ⟩∘ᴹ⟨ id⊗ᵉ-hom g′ g)
  ○ᴹ MR.center (⟺ᴹ (⊗-split f g′) ○ᴹ ⊗-split′ f g′)
  ○ᴹ ⟺ᴹ (MR.center reflᴹ)
  ○ᴹ ⟺ᴹ (⊗-split f′ g′ ⟩∘ᴹ⟨ ⊗-split f g)

------------------------------------------------------------------------
-- Associator naturality

-- Re-bracketing the interface sum: `δ-unique` twice, then each of the three
-- leaves is the branch its own injection selects.
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

private
  -- Naturality in one factor at a time.  The other two factors are `idᴹ`, so
  -- the two collapses reduce both sides to the one machine's own state and the
  -- whole content is `tstep-α`.
  natˡ : (f : Machine A B)
       → (α⇒ᴹ ∘ᴹ ((f ⊗ᵉ idᴹ {C}) ⊗ᵉ idᴹ {D})) ≈ᴹ ((f ⊗ᵉ idᴹ {C + D}) ∘ᴹ α⇒ᴹ)
  natˡ f = (reflᴹ⟩∘ᴹ⟨ (⊗ᵉ-resp-≈ᴹ (≲⇒≈ᴹ (⊗idᵉ-collapse f)) reflᴹ
                       ○ᴹ ≲⇒≈ᴹ (⊗idᵉ-collapse _)))
         ○ᴹ ≲⇒≈ᴹ (pure-∘ˡ α+⇒ _)
         ○ᴹ ≲⇒≈ᴹ (mk-cong (tstep-α ○ (tstep-cong refl tstep-id ⟩∘⟨refl)))
         ○ᴹ ≲⇒≈ᴹ˘ (pure-∘ʳ α+⇒ _)
         ○ᴹ (≲⇒≈ᴹ˘ (⊗idᵉ-collapse f) ⟩∘ᴹ⟨reflᴹ)

  natᶜ : (g : Machine C D)
       → (α⇒ᴹ ∘ᴹ ((idᴹ {A} ⊗ᵉ g) ⊗ᵉ idᴹ {E})) ≈ᴹ ((idᴹ {A} ⊗ᵉ (g ⊗ᵉ idᴹ {E})) ∘ᴹ α⇒ᴹ)
  natᶜ g = (reflᴹ⟩∘ᴹ⟨ (⊗ᵉ-resp-≈ᴹ (≲⇒≈ᴹ (id⊗ᵉ-collapse g)) reflᴹ
                       ○ᴹ ≲⇒≈ᴹ (⊗idᵉ-collapse _)))
         ○ᴹ ≲⇒≈ᴹ (pure-∘ˡ α+⇒ _)
         ○ᴹ ≲⇒≈ᴹ (mk-cong tstep-α)
         ○ᴹ ≲⇒≈ᴹ˘ (pure-∘ʳ α+⇒ _)
         ○ᴹ (⟺ᴹ (⊗ᵉ-resp-≈ᴹ reflᴹ (≲⇒≈ᴹ (⊗idᵉ-collapse g))
                 ○ᴹ ≲⇒≈ᴹ (id⊗ᵉ-collapse _)) ⟩∘ᴹ⟨reflᴹ)

  natʳ : (h : Machine E F)
       → (α⇒ᴹ ∘ᴹ (idᴹ {A + C} ⊗ᵉ h)) ≈ᴹ ((idᴹ {A} ⊗ᵉ (idᴹ {C} ⊗ᵉ h)) ∘ᴹ α⇒ᴹ)
  natʳ h = (reflᴹ⟩∘ᴹ⟨ ≲⇒≈ᴹ (id⊗ᵉ-collapse h))
         ○ᴹ ≲⇒≈ᴹ (pure-∘ˡ α+⇒ _)
         ○ᴹ ≲⇒≈ᴹ (mk-cong ((refl⟩∘⟨ ⟺ (tstep-cong tstep-id refl)) ○ tstep-α))
         ○ᴹ ≲⇒≈ᴹ˘ (pure-∘ʳ α+⇒ _)
         ○ᴹ (⟺ᴹ (⊗ᵉ-resp-≈ᴹ reflᴹ (≲⇒≈ᴹ (id⊗ᵉ-collapse h))
                 ○ᴹ ≲⇒≈ᴹ (id⊗ᵉ-collapse _)) ⟩∘ᴹ⟨reflᴹ)

assoc-commuteᴹ : {f : Machine A B} {g : Machine C D} {h : Machine E F}
               → (α⇒ᴹ ∘ᴹ ((f ⊗ᵉ g) ⊗ᵉ h)) ≈ᴹ ((f ⊗ᵉ (g ⊗ᵉ h)) ∘ᴹ α⇒ᴹ)
assoc-commuteᴹ {f = f} {g} {h} =
    (reflᴹ⟩∘ᴹ⟨ decompˡ)
  ○ᴹ ℳ.sym-assoc ○ᴹ (ℳ.sym-assoc ⟩∘ᴹ⟨reflᴹ)
  ○ᴹ ((natˡ f ⟩∘ᴹ⟨reflᴹ) ⟩∘ᴹ⟨reflᴹ)
  ○ᴹ (ℳ.assoc ⟩∘ᴹ⟨reflᴹ) ○ᴹ ((reflᴹ⟩∘ᴹ⟨ natᶜ g) ⟩∘ᴹ⟨reflᴹ) ○ᴹ (ℳ.sym-assoc ⟩∘ᴹ⟨reflᴹ)
  ○ᴹ ℳ.assoc ○ᴹ (reflᴹ⟩∘ᴹ⟨ natʳ h) ○ᴹ ℳ.sym-assoc
  ○ᴹ (⟺ᴹ decompʳ ⟩∘ᴹ⟨reflᴹ)
  where
    decompˡ = ⊗-split (f ⊗ᵉ g) h
            ○ᴹ ((⊗ᵉ-resp-≈ᴹ (⊗-split f g) reflᴹ ○ᴹ ⊗idᵉ-hom _ _) ⟩∘ᴹ⟨reflᴹ)

    decompʳ = ⊗-split f (g ⊗ᵉ h)
            ○ᴹ (reflᴹ⟩∘ᴹ⟨ (⊗ᵉ-resp-≈ᴹ reflᴹ (⊗-split g h) ○ᴹ id⊗ᵉ-hom _ _))
            ○ᴹ ℳ.sym-assoc
