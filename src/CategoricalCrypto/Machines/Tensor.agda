{-# OPTIONS --safe --without-K #-}

-- The interface tensor. `_⊛_` pairs states; this pairs interfaces.

open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Subcategory
import Categories.Category.Cocartesian.Ext as CE
import Categories.Category.Monoidal.Distributive as MD
import Categories.Category.Monoidal.Distributive.Properties as MDP
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

import Relation.Binary.Construct.Closure.Equivalence as EqC

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Frame as Frame
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.Machines.Tensor
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e)
  (dist : MD.MonoidalDistributive 𝒱) (𝒫 : WideSymmetricMonoidalSubcategory 𝒱) where

open SymmetricMonoidalCategory 𝒱
open Core 𝒱
open Frame 𝒱
open MD.MonoidalDistributive dist
open CE U cocartesian
open MDP 𝒱 dist
open MonoidalUtilities.Shorthands monoidal
open WideSymmetricMonoidalSubcategory 𝒫
open Sim 𝒱 𝒫

open import Categories.Category.Monoidal.Reassociation monoidal
open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Morphism.Reasoning U

private variable A B C D P Q R S T X Y : Obj

tstep : (X ⊗₀ A ⇒ Y ⊗₀ B) → (X ⊗₀ C ⇒ Y ⊗₀ D) → X ⊗₀ (A + C) ⇒ Y ⊗₀ (B + D)
tstep k l = distributeˡ ∘ (k +₁ l) ∘ δ⇐

infixr 10 _⊗ᵉ_

_⊗ᵉ_ : Machine A B → Machine C D → Machine (A + C) (B + D)
f ⊗ᵉ g = mk (state f ⊛ state g) (tstep (onL (step f)) (onR (step g)))

--------------------------------------------------------------------------------
-- `tstep` properties

tstep-cong : {k k′ : X ⊗₀ A ⇒ Y ⊗₀ B} {l l′ : X ⊗₀ C ⇒ Y ⊗₀ D}
           → k ≈ k′ → l ≈ l′ → tstep k l ≈ tstep k′ l′
tstep-cong e₁ e₂ = refl⟩∘⟨ +₁-cong₂ e₁ e₂ ⟩∘⟨refl

tstep-i₁ : {k : X ⊗₀ A ⇒ Y ⊗₀ B} {l : X ⊗₀ C ⇒ Y ⊗₀ D}
         → tstep k l ∘ id ⊗₁ i₁ ≈ id ⊗₁ i₁ ∘ k
tstep-i₁ = assoc ○ refl⟩∘⟨ (pullʳ δ⇐-i₁ ○ +₁∘i₁) ○ pullˡ inject₁

tstep-i₂ : {k : X ⊗₀ A ⇒ Y ⊗₀ B} {l : X ⊗₀ C ⇒ Y ⊗₀ D}
         → tstep k l ∘ id ⊗₁ i₂ ≈ id ⊗₁ i₂ ∘ l
tstep-i₂ = assoc ○ refl⟩∘⟨ (pullʳ δ⇐-i₂ ○ +₁∘i₂) ○ pullˡ inject₂

tstep-id : tstep (id {X ⊗₀ A}) (id {X ⊗₀ C}) ≈ id
tstep-id = refl⟩∘⟨ elimˡ id+₁id ○ distributeˡ.isoʳ

tstep-∘ : {k₂ : T ⊗₀ B ⇒ X ⊗₀ C} {l₂ : T ⊗₀ Q ⇒ X ⊗₀ R}
          {k₁ : S ⊗₀ A ⇒ T ⊗₀ B} {l₁ : S ⊗₀ P ⇒ T ⊗₀ Q}
        → tstep k₂ l₂ ∘ tstep k₁ l₁ ≈ tstep (k₂ ∘ k₁) (l₂ ∘ l₁)
tstep-∘ = assoc ○ refl⟩∘⟨ assoc ○ refl⟩∘⟨ refl⟩∘⟨ cancelˡ distributeˡ.isoˡ ○ refl⟩∘⟨ pullˡ +₁∘+₁

tstep-pad : (θ : S ⇒ T) → tstep (θ ⊗₁ id) (θ ⊗₁ id) ≈ θ ⊗₁ id {X + Y}
tstep-pad θ = δ-unique (tstep-i₁ ○ ⟺ whisker-comm) (tstep-i₂ ○ ⟺ whisker-comm)

tstep-sim : {v : X ⇒ Y}
            {k : X ⊗₀ A ⇒ X ⊗₀ B} {k′ : Y ⊗₀ A ⇒ Y ⊗₀ B}
            {l : X ⊗₀ C ⇒ X ⊗₀ D} {l′ : Y ⊗₀ C ⇒ Y ⊗₀ D}
          → v ⊗₁ id ∘ k ≈ k′ ∘ v ⊗₁ id → v ⊗₁ id ∘ l ≈ l′ ∘ v ⊗₁ id
          → v ⊗₁ id ∘ tstep k l ≈ tstep k′ l′ ∘ v ⊗₁ id
tstep-sim {v = v} e₁ e₂ =
  ⟺ (tstep-pad v) ⟩∘⟨refl ○ tstep-∘ ○ tstep-cong e₁ e₂ ○ ⟺ tstep-∘ ○ refl⟩∘⟨ tstep-pad v

tstep-str : (h : A ⇒ B) (k : C ⇒ D) → tstep (id {X} ⊗₁ h) (id ⊗₁ k) ≈ id ⊗₁ (h +₁ k)
tstep-str h k = δ-unique (tstep-i₁ ○ merge₂ʳ ○ ⟺ (merge₂ʳ ○ refl⟩⊗⟨ +₁∘i₁))
                         (tstep-i₂ ○ merge₂ʳ ○ ⟺ (merge₂ʳ ○ refl⟩⊗⟨ +₁∘i₂))

tstep-relabel : (s : C ⇒ D) → tstep (id {X ⊗₀ A}) (id ⊗₁ s) ≈ id ⊗₁ (id +₁ s)
tstep-relabel s = tstep-cong (⟺ ⊗.identity) Equiv.refl ○ tstep-str id s

onL-tstep : {k : P ⊗₀ A ⇒ P ⊗₀ B} {l : P ⊗₀ C ⇒ P ⊗₀ D}
          → onL {Q = Q} (tstep k l) ≈ tstep (onL k) (onL l)
onL-tstep = δ-unique (onL-branch tstep-i₁ ○ ⟺ tstep-i₁) (onL-branch tstep-i₂ ○ ⟺ tstep-i₂)

onR-tstep : {k : Q ⊗₀ A ⇒ Q ⊗₀ B} {l : Q ⊗₀ C ⇒ Q ⊗₀ D}
          → onR {P = P} (tstep k l) ≈ tstep (onR k) (onR l)
onR-tstep = δ-unique (onR-branch tstep-i₁ ○ ⟺ tstep-i₁) (onR-branch tstep-i₂ ○ ⟺ tstep-i₂)

--------------------------------------------------------------------------------
-- `⊗ᵉ` properties

⊗ᵉ-resp-≲ : {f h : Machine A B} {g i : Machine C D} → f ≲ h → g ≲ i → f ⊗ᵉ g ≲ h ⊗ᵉ i
⊗ᵉ-resp-≲ {f = f} {h} {g} {i} u v = record
  { θ       = θ u ⊗₁ θ v
  ; θ-selected = selected-⊗₁ (θ-selected u) (θ-selected v)
  ; θ-point = ⊛-point₂ (state f) (state h) (state g) (state i) (θ-point u) (θ-point v)
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
  pure-∘ˡ h M = collapseˡ (refl⟩∘⟨ onL-id⊗ h ⟩∘⟨refl ○ pullˡ whisker-comm
                           ○ assoc ○ refl⟩∘⟨ onR-collapseˡ ○ sym-assoc)

  pure-∘ʳ : (h : A ⇒ B) (M : Machine B C) → M ∘ᴹ pureᴹ h ≲ mk (state M) (step M ∘ id ⊗₁ h)
  pure-∘ʳ h M = collapseʳ (refl⟩∘⟨ refl⟩∘⟨ onR-id⊗ h ○ pullˡ onL-collapseʳ ○ assoc
                           ○ refl⟩∘⟨ whisker-comm ○ sym-assoc)

⊗ᵉ-pureᴹ : (h : A ⇒ B) (k : C ⇒ D) → pureᴹ h ⊗ᵉ pureᴹ k ≲ pureᴹ (h +₁ k)
⊗ᵉ-pureᴹ h k = collapseˡ (refl⟩∘⟨ (tstep-cong (onL-id⊗ h) (onR-id⊗ k) ○ tstep-str h k) ○ whisker-comm)

⊗ᵉ-identity : (idᴹ {A} ⊗ᵉ idᴹ {B}) ≲ idᴹ
⊗ᵉ-identity = collapseˡ (refl⟩∘⟨ (tstep-cong onL-id onR-id ○ tstep-id) ○ identityʳ ○ ⟺ identityˡ)

pure⊗-stateˡ : (h : A ⇒ B) (M : Machine C D) → pureᴹ h ⊗ᵉ M ≲ mk (state M) (tstep (id ⊗₁ h) (step M))
pure⊗-stateˡ h M =
  collapseˡ (refl⟩∘⟨ tstep-cong (onL-id⊗ h) Equiv.refl ○ tstep-sim whisker-comm onR-collapseˡ)

pure⊗-stateʳ : (M : Machine A B) (h : C ⇒ D) → M ⊗ᵉ pureᴹ h ≲ mk (state M) (tstep (step M) (id ⊗₁ h))
pure⊗-stateʳ M h =
  collapseʳ (refl⟩∘⟨ tstep-cong Equiv.refl (onR-id⊗ h) ○ tstep-sim onL-collapseʳ whisker-comm)

α⇒ᴹ : Machine ((A + B) + C) (A + (B + C))
α⇒ᴹ = pureᴹ α+⇒

α⇐ᴹ : Machine (A + (B + C)) ((A + B) + C)
α⇐ᴹ = pureᴹ α+⇐

σᴹ : Machine (A + B) (B + A)
σᴹ = pureᴹ +-swap

λ⇒ᴹ : Machine (⊥ + A) A
λ⇒ᴹ = pureᴹ ⊕.unitorˡ.from

ρ⇒ᴹ : Machine (A + ⊥) A
ρ⇒ᴹ = pureᴹ ⊕.unitorʳ.from
