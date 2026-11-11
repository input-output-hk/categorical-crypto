{-# OPTIONS --safe --without-K #-}

-- The interface tensor. `_⊛_` pairs states; this pairs interfaces.

open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Subcategory
import Categories.Category.Cocartesian.Ext as CE
import Categories.Category.Monoidal.Distributive as MD
import Categories.Category.Monoidal.Distributive.Properties as MDP

import Relation.Binary.Construct.Closure.Equivalence as EqC

import CategoricalCrypto.Machines.Category as MCat
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.Machines.Tensor
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e)
  (dist : MD.MonoidalDistributive 𝒱) (𝒫 : WideSymmetricMonoidalSubcategory 𝒱) where

open SymmetricMonoidalCategory 𝒱
open Core 𝒱
open MCat 𝒱 𝒫
open MD.MonoidalDistributive dist
open CE U cocartesian
open MDP 𝒱 dist
open WideSymmetricMonoidalSubcategory 𝒫
open Sim 𝒱 𝒫

open import Categories.Category.Monoidal.Reassociation monoidal
open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Category.Monoidal.Symmetric.Properties.Ext symmetric
open import Categories.Morphism.Reasoning U

private variable A B C D : Obj

infixr 10 _⊗ᵉ_

_⊗ᵉ_ : Machine A B → Machine C D → Machine (A + C) (B + D)
f ⊗ᵉ g = mk (state f ⊛ state g) (tstep (onL (step f)) (onR (step g)))

--------------------------------------------------------------------------------

-- `⊗ᵉ` properties

⊗ᵉ-resp-≲ : {f h : Machine A B} {g i : Machine C D} → f ≲ h → g ≲ i → f ⊗ᵉ g ≲ h ⊗ᵉ i
⊗ᵉ-resp-≲ {f = f} {h} {g} {i} u v = record
  { θ       = θ u ⊗₁ θ v
  ; θ-selected = selected-⊗₁ (θ-selected u) (θ-selected v)
  ; θ-point = ⊛-∘-point (θ-point u) (θ-point v)
  ; θ-step  = tstep-sim (onL-sim (θ-step u)) (onR-sim (θ-step v))
  }

⊗ᵉ-resp-≈ᴹ : {f h : Machine A B} {g i : Machine C D} → f ≈ᴹ h → g ≈ᴹ i → f ⊗ᵉ g ≈ᴹ h ⊗ᵉ i
⊗ᵉ-resp-≈ᴹ {g = g} e₁ e₂ =
  EqC.gmap (_⊗ᵉ g) (λ s → ⊗ᵉ-resp-≲ s ≲-refl) e₁ ○ᴹ EqC.gmap (_ ⊗ᵉ_) (⊗ᵉ-resp-≲ ≲-refl) e₂

------------------------------------------------------------------------
-- Pure machines

pureᴹ : A ⇒ B → Machine A B
pureᴹ f = mk Iˢ (id ⊗₁ f)

pureᴹ-cong : {f g : A ⇒ B} → f ≈ g → pureᴹ f ≲ pureᴹ g
pureᴹ-cong eq = mk-cong (refl⟩⊗⟨ eq)

pureᴹ-id : pureᴹ (id {A}) ≲ idᴹ
pureᴹ-id = mk-cong ⊗.identity

opaque
  unfolding _∘ᴹ_

  pureᴹ-∘ : (g : B ⇒ C) (f : A ⇒ B) → pureᴹ g ∘ᴹ pureᴹ f ≲ pureᴹ (g ∘ f)
  pureᴹ-∘ g f = collapseˡ (refl⟩∘⟨ (onL-id⊗ g ⟩∘⟨ onR-id⊗ f ○ merge₂ˡ) ○ whisker-comm)

  pure-∘ˡ : (h : B ⇒ C) (M : Machine A B) → pureᴹ h ∘ᴹ M ≲ mk (state M) (id ⊗₁ h ∘ step M)
  pure-∘ˡ h M = collapseˡ (refl⟩∘⟨ onL-id⊗ h ⟩∘⟨refl ○ pullˡ whisker-comm ○ assoc ○ refl⟩∘⟨ onR-collapseˡ ○ sym-assoc)

  pure-∘ʳ : (h : A ⇒ B) (M : Machine B C) → M ∘ᴹ pureᴹ h ≲ mk (state M) (step M ∘ id ⊗₁ h)
  pure-∘ʳ h M = collapseʳ (refl⟩∘⟨ refl⟩∘⟨ onR-id⊗ h ○ pullˡ onL-collapseʳ ○ assoc ○ refl⟩∘⟨ whisker-comm ○ sym-assoc)

pure-∘both : (l : B ⇒ C) (r : D ⇒ A) (M : Machine A B)
           → pureᴹ l ∘ᴹ M ∘ᴹ pureᴹ r ≲ mk (state M) (id ⊗₁ l ∘ step M ∘ id ⊗₁ r)
pure-∘both l r M = ≲-trans (∘ᴹ-resp-≲ ≲-refl (pure-∘ʳ r M)) (pure-∘ˡ l (mk (state M) (step M ∘ id ⊗₁ r)))

⊗ᵉ-pureᴹ : (h : A ⇒ B) (k : C ⇒ D) → pureᴹ h ⊗ᵉ pureᴹ k ≲ pureᴹ (h +₁ k)
⊗ᵉ-pureᴹ h k = collapseˡ (refl⟩∘⟨ (tstep-cong (onL-id⊗ h) (onR-id⊗ k) ○ ⊗-+₁ h k) ○ whisker-comm)

⊗ᵉ-identity : (idᴹ {A} ⊗ᵉ idᴹ {B}) ≲ idᴹ
⊗ᵉ-identity = collapseˡ (refl⟩∘⟨ (tstep-cong onL-id onR-id ○ tstep-id) ○ id-comm)

⊗idᵉ-collapse : (f : Machine A B) → f ⊗ᵉ idᴹ {C} ≲ mk (state f) (tstep (step f) id)
⊗idᵉ-collapse f = collapseʳ (tstep-sim onL-collapseʳ (refl⟩∘⟨ onR-id ○ id-comm))

id⊗ᵉ-collapse : (g : Machine C D) → idᴹ {A} ⊗ᵉ g ≲ mk (state g) (tstep id (step g))
id⊗ᵉ-collapse g = collapseˡ (tstep-sim (refl⟩∘⟨ onL-id ○ id-comm) onR-collapseˡ)

pure⊗-stateˡ : (h : A ⇒ B) (M : Machine C D) → pureᴹ h ⊗ᵉ M ≲ mk (state M) (tstep (id ⊗₁ h) (step M))
pure⊗-stateˡ h M =
  collapseˡ (refl⟩∘⟨ tstep-cong (onL-id⊗ h) Equiv.refl ○ tstep-sim whisker-comm onR-collapseˡ)

pure⊗-stateʳ : (M : Machine A B) (h : C ⇒ D) → M ⊗ᵉ pureᴹ h ≲ mk (state M) (tstep (step M) (id ⊗₁ h))
pure⊗-stateʳ M h =
  collapseʳ (refl⟩∘⟨ tstep-cong Equiv.refl (onR-id⊗ h) ○ tstep-sim onL-collapseʳ whisker-comm)

α⇒ᴹ : Machine ((A + B) + C) (A + (B + C))
α⇒ᴹ = pureᴹ +-assocˡ

α⇐ᴹ : Machine (A + (B + C)) ((A + B) + C)
α⇐ᴹ = pureᴹ +-assocʳ

σᴹ : Machine (A + B) (B + A)
σᴹ = pureᴹ +-swap

λ⇒ᴹ : Machine (⊥ + A) A
λ⇒ᴹ = pureᴹ ⊕.unitorˡ.from

ρ⇒ᴹ : Machine (A + ⊥) A
ρ⇒ᴹ = pureᴹ ⊕.unitorʳ.from
