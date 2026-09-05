{-# OPTIONS --safe --without-K #-}

-- The interface tensor's unit and braiding coherence.  Every law here is its
-- `+`-monoidal instance conjugated by `pureᴹ`: the structural machines are pure,
-- `pureᴹ` is a monoidal functor (`⊗ᵉ-pureˡ`/`⊗ᵉ-pureʳ`/`pureᴹ-∘`), so
-- `triangleᴹ`/`pentagonᴹ`/`hexagonᴹ` are one `pureᴹ-cong` each.
--
-- The two naturalities are not: they relate a structural machine to an
-- arbitrary one.  The unitors' hold because `X ⊗₀ ⊥` is initial (`⊥-unique`),
-- so the summand that would carry the other machine cannot fire; the
-- braiding's is the state braiding `σ⇒` exchanging the two state actions
-- (`σ-onL`/`σ-onR`) while `tstep-swap` exchanges the interface summands.

open import Categories.Category.Core
open import Categories.Category.Monoidal.Braided
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

open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Morphism.Reasoning U

private
  module ⊕Sym = Symmetric (Cocart.CocartesianSymmetricMonoidal.+-symmetric U cocartesian)
  module ⊕Br = Braided ⊕Sym.braided
  module ℳ = Category Mealy-Category

open ℳ.HomReasoning using ()
  renaming (_⟩∘⟨_ to _⟩∘ᴹ⟨_; refl⟩∘⟨_ to reflᴹ⟩∘ᴹ⟨_; _⟩∘⟨refl to _⟩∘ᴹ⟨reflᴹ)

private variable A B C D W X Y Z : Obj

------------------------------------------------------------------------
-- `tstep` is functorial

tstep-∘ : {S T V A₁ A₂ A₃ B₁ B₂ B₃ : Obj}
          {k₂ : T ⊗₀ A₂ ⇒ V ⊗₀ A₃} {l₂ : T ⊗₀ B₂ ⇒ V ⊗₀ B₃}
          {k₁ : S ⊗₀ A₁ ⇒ T ⊗₀ A₂} {l₁ : S ⊗₀ B₁ ⇒ T ⊗₀ B₂}
        → tstep k₂ l₂ ∘ tstep k₁ l₁ ≈ tstep (k₂ ∘ k₁) (l₂ ∘ l₁)
tstep-∘ = assoc ○ (refl⟩∘⟨ assoc)
        ○ (refl⟩∘⟨ refl⟩∘⟨ cancelˡ distributeˡ.isoˡ)
        ○ (refl⟩∘⟨ pullˡ +₁∘+₁)

------------------------------------------------------------------------
-- The structural machines

λ⇒ᴹ : Machine (⊥ + A) A
λ⇒ᴹ = pureᴹ ⊕.unitorˡ.from

λ⇐ᴹ : Machine A (⊥ + A)
λ⇐ᴹ = pureᴹ ⊕.unitorˡ.to

ρ⇒ᴹ : Machine (A + ⊥) A
ρ⇒ᴹ = pureᴹ ⊕.unitorʳ.from

ρ⇐ᴹ : Machine A (A + ⊥)
ρ⇐ᴹ = pureᴹ ⊕.unitorʳ.to

-- `idᴹ` and `pureᴹ id` differ only in their step, so they are interchangeable
-- under `_⊗ᵉ_` without a congruence for it.
⊗ᵉ-pureˡ : (h : C ⇒ D) → (idᴹ {A} ⊗ᵉ pureᴹ h) ≲ pureᴹ (id +₁ h)
⊗ᵉ-pureˡ h = ≲-trans (mk-cong (tstep-cong (onL-cong (⟺ ⊗.identity)) refl))
                     (⊗ᵉ-pureᴹ id h)

⊗ᵉ-pureʳ : (h : A ⇒ B) → (pureᴹ h ⊗ᵉ idᴹ {C}) ≲ pureᴹ (h +₁ id)
⊗ᵉ-pureʳ h = ≲-trans (mk-cong (tstep-cong refl (onR-cong (⟺ ⊗.identity))))
                     (⊗ᵉ-pureᴹ h id)

------------------------------------------------------------------------
-- Coherence: every law is its base instance conjugated by `pureᴹ`

pure-iso : {h : A ⇒ B} {h⁻ : B ⇒ A} → h⁻ ∘ h ≈ id → (pureᴹ h⁻ ∘ᴹ pureᴹ h) ≲ idᴹ
pure-iso eq = ≲-trans (pureᴹ-∘ _ _) (≲-trans (pureᴹ-cong eq) pureᴹ-id)

λᴹ-isoˡ : (λ⇐ᴹ ∘ᴹ λ⇒ᴹ {A}) ≲ idᴹ
λᴹ-isoˡ = pure-iso ⊕.unitorˡ.isoˡ

λᴹ-isoʳ : (λ⇒ᴹ ∘ᴹ λ⇐ᴹ {A}) ≲ idᴹ
λᴹ-isoʳ = pure-iso ⊕.unitorˡ.isoʳ

ρᴹ-isoˡ : (ρ⇐ᴹ ∘ᴹ ρ⇒ᴹ {A}) ≲ idᴹ
ρᴹ-isoˡ = pure-iso ⊕.unitorʳ.isoˡ

ρᴹ-isoʳ : (ρ⇒ᴹ ∘ᴹ ρ⇐ᴹ {A}) ≲ idᴹ
ρᴹ-isoʳ = pure-iso ⊕.unitorʳ.isoʳ

αᴹ-isoˡ : (α⇐ᴹ ∘ᴹ α⇒ᴹ {A} {B} {C}) ≲ idᴹ
αᴹ-isoˡ = pure-iso ⊕.associator.isoˡ

αᴹ-isoʳ : (α⇒ᴹ ∘ᴹ α⇐ᴹ {A} {B} {C}) ≲ idᴹ
αᴹ-isoʳ = pure-iso ⊕.associator.isoʳ

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
         ○ᴹ ≲⇒≈ᴹ (≲-trans (pureᴹ-∘ _ _) (pureᴹ-cong ⊕Br.hexagon₁))
         ○ᴹ ≲⇒≈ᴹ˘ (pureᴹ-∘ _ _)
         ○ᴹ (reflᴹ⟩∘ᴹ⟨ ≲⇒≈ᴹ˘ (pureᴹ-∘ _ _))

------------------------------------------------------------------------
-- Unitor naturality

private
  ρ-i₁ : id {X} ⊗₁ ⊕.unitorʳ.from {A} ∘ id ⊗₁ i₁ ≈ id
  ρ-i₁ = merge₂ʳ ○ (refl⟩⊗⟨ ⊕.unitorʳ.isoʳ) ○ ⊗.identity

  λ-i₂ : id {X} ⊗₁ ⊕.unitorˡ.from {A} ∘ id ⊗₁ i₂ ≈ id
  λ-i₂ = merge₂ʳ ○ (refl⟩⊗⟨ ⊕.unitorˡ.isoʳ) ○ ⊗.identity

-- Cutting the empty summand: the other branch cannot fire, because `X ⊗₀ ⊥` is
-- initial.
tstep-ρ : {k : X ⊗₀ A ⇒ X ⊗₀ B} {l : X ⊗₀ ⊥ ⇒ X ⊗₀ ⊥}
        → id ⊗₁ ⊕.unitorʳ.from ∘ tstep k l ≈ k ∘ id ⊗₁ ⊕.unitorʳ.from
tstep-ρ = δ-unique (pullʳ tstep-i₁ ○ pullˡ ρ-i₁ ○ identityˡ
                    ○ ⟺ (pullʳ ρ-i₁ ○ identityʳ)) ⊥-unique

tstep-λ : {k : X ⊗₀ ⊥ ⇒ X ⊗₀ ⊥} {l : X ⊗₀ A ⇒ X ⊗₀ B}
        → id ⊗₁ ⊕.unitorˡ.from ∘ tstep k l ≈ l ∘ id ⊗₁ ⊕.unitorˡ.from
tstep-λ = δ-unique ⊥-unique
                   (pullʳ tstep-i₂ ○ pullˡ λ-i₂ ○ identityˡ
                    ○ ⟺ (pullʳ λ-i₂ ○ identityʳ))

unitorˡ-commuteᴹ : {f : Machine A B} → (λ⇒ᴹ ∘ᴹ (idᴹ {⊥} ⊗ᵉ f)) ≈ᴹ (f ∘ᴹ λ⇒ᴹ)
unitorˡ-commuteᴹ {f = f} =
    ≲⇒≈ᴹ (pure-∘ˡ ⊕.unitorˡ.from (idᴹ ⊗ᵉ f))
  ○ᴹ ≲⇒≈ᴹ (collapseˡ ((refl⟩∘⟨ tstep-λ) ○ pullˡ onR-collapseˡ ○ assoc
                      ○ (refl⟩∘⟨ ⟺ (pad-transport λ⇒ ⊕.unitorˡ.from)) ○ sym-assoc))
  ○ᴹ ≲⇒≈ᴹ˘ (pure-∘ʳ ⊕.unitorˡ.from f)

unitorʳ-commuteᴹ : {f : Machine A B} → (ρ⇒ᴹ ∘ᴹ (f ⊗ᵉ idᴹ {⊥})) ≈ᴹ (f ∘ᴹ ρ⇒ᴹ)
unitorʳ-commuteᴹ {f = f} =
    ≲⇒≈ᴹ (pure-∘ˡ ⊕.unitorʳ.from (f ⊗ᵉ idᴹ))
  ○ᴹ ≲⇒≈ᴹ (collapseʳ ((refl⟩∘⟨ tstep-ρ) ○ pullˡ onL-collapseʳ ○ assoc
                      ○ (refl⟩∘⟨ ⟺ (pad-transport ρ⇒ ⊕.unitorʳ.from)) ○ sym-assoc))
  ○ᴹ ≲⇒≈ᴹ˘ (pure-∘ʳ ⊕.unitorʳ.from f)

------------------------------------------------------------------------
-- Braiding naturality

-- Swapping the interface summands swaps the two arms.
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
  ○ᴹ ≲⇒≈ᴹ (sim σ⇒ pure-σ⇒ discard-σ point-σ
             (pullˡ (⟺ (pad-transport σ⇒ +-swap)) ○ assoc
              ○ (refl⟩∘⟨ tstep-sim σ-onL σ-onR) ○ sym-assoc ○ (tstep-swap ⟩∘⟨refl)))
  ○ᴹ ≲⇒≈ᴹ˘ (pure-∘ʳ +-swap (g ⊗ᵉ f))
  where
    discard-σ : discard (state g ⊛ state f) ∘ σ⇒ ≈ discard (state f ⊛ state g)
    discard-σ = pullʳ (⟺ (braiding.⇒.commute _)) ○ pullˡ (refl⟩∘⟨ σ-unit ○ identityʳ)

    point-σ : σ⇒ ∘ point (state f ⊛ state g) ≈ point (state g ⊛ state f)
    point-σ = pullˡ (braiding.⇒.commute _) ○ assoc
            ○ (refl⟩∘⟨ (σ-unit ⟩∘⟨refl ○ identityˡ))

------------------------------------------------------------------------
-- Collapsing the trivial state factor of a one-sided tensor

⊗idᵉ-collapse : (f : Machine A B) → (f ⊗ᵉ idᴹ {C}) ≲ mk (state f) (tstep (step f) id)
⊗idᵉ-collapse f =
  collapseʳ (tstep-sim onL-collapseʳ ((refl⟩∘⟨ onR-id) ○ identityʳ ○ ⟺ identityˡ))

id⊗ᵉ-collapse : (g : Machine C D) → (idᴹ {A} ⊗ᵉ g) ≲ mk (state g) (tstep id (step g))
id⊗ᵉ-collapse g =
  collapseˡ (tstep-sim ((refl⟩∘⟨ onL-id) ○ identityʳ ○ ⟺ identityˡ) onR-collapseˡ)
