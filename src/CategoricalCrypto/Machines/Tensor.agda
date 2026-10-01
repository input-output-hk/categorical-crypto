{-# OPTIONS --safe --without-K #-}

-- The interface tensor.  `_⊛_` pairs STATES; this pairs INTERFACES, by the
-- coproduct of the base's distributive structure.  A map out of a distributed
-- sum is its two components (`δ-unique`), so the ⊕-side equations are branch
-- goals rather than coherence chains.

open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Pure
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
  (dist : MD.MonoidalDistributive 𝒱) (𝒫 : PureSub 𝒱) where

open SymmetricMonoidalCategory 𝒱
open Core 𝒱
open Frame 𝒱
open MD.MonoidalDistributive dist
open CE U cocartesian
open MDP 𝒱 dist
open MonoidalUtilities.Shorthands monoidal
open PureSub 𝒫
open Sim 𝒱 𝒫

open import Categories.Category.Monoidal.Properties.Ext monoidal
open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Morphism.Reasoning U

private variable A B C D P Q X Y : Obj

------------------------------------------------------------------------
-- Acting on a sum interface

-- The codomain state is free: a `tstep` is also the `+`-side relabelling a
-- state-and-loop-variable transfer acts by (`Machines.Iteration`).
tstep : (X ⊗₀ A ⇒ Y ⊗₀ B) → (X ⊗₀ C ⇒ Y ⊗₀ D) → X ⊗₀ (A + C) ⇒ Y ⊗₀ (B + D)
tstep k l = distributeˡ ∘ (k +₁ l) ∘ δ⇐

tstep-cong : {k k′ : X ⊗₀ A ⇒ Y ⊗₀ B} {l l′ : X ⊗₀ C ⇒ Y ⊗₀ D}
           → k ≈ k′ → l ≈ l′ → tstep k l ≈ tstep k′ l′
tstep-cong e₁ e₂ = refl⟩∘⟨ +₁-cong₂ e₁ e₂ ⟩∘⟨refl

tstep-i₁ : {k : X ⊗₀ A ⇒ Y ⊗₀ B} {l : X ⊗₀ C ⇒ Y ⊗₀ D}
         → tstep k l ∘ id ⊗₁ i₁ ≈ id ⊗₁ i₁ ∘ k
tstep-i₁ = assoc ○ (refl⟩∘⟨ (pullʳ δ⇐-i₁ ○ +₁∘i₁)) ○ pullˡ inject₁

tstep-i₂ : {k : X ⊗₀ A ⇒ Y ⊗₀ B} {l : X ⊗₀ C ⇒ Y ⊗₀ D}
         → tstep k l ∘ id ⊗₁ i₂ ≈ id ⊗₁ i₂ ∘ l
tstep-i₂ = assoc ○ (refl⟩∘⟨ (pullʳ δ⇐-i₂ ○ +₁∘i₂)) ○ pullˡ inject₂

tstep-id : tstep (id {X ⊗₀ A}) (id {X ⊗₀ C}) ≈ id
tstep-id = (refl⟩∘⟨ elimˡ +₁-id) ○ distributeˡ.isoʳ

tstep-∘ : {S T V A₁ A₂ A₃ B₁ B₂ B₃ : Obj}
          {k₂ : T ⊗₀ A₂ ⇒ V ⊗₀ A₃} {l₂ : T ⊗₀ B₂ ⇒ V ⊗₀ B₃}
          {k₁ : S ⊗₀ A₁ ⇒ T ⊗₀ A₂} {l₁ : S ⊗₀ B₁ ⇒ T ⊗₀ B₂}
        → tstep k₂ l₂ ∘ tstep k₁ l₁ ≈ tstep (k₂ ∘ k₁) (l₂ ∘ l₁)
tstep-∘ = assoc ○ (refl⟩∘⟨ assoc)
        ○ (refl⟩∘⟨ refl⟩∘⟨ cancelˡ distributeˡ.isoˡ)
        ○ (refl⟩∘⟨ pullˡ +₁∘+₁)

tstep-str : (h : A ⇒ B) (k : C ⇒ D) → tstep (id {X} ⊗₁ h) (id ⊗₁ k) ≈ id ⊗₁ (h +₁ k)
tstep-str h k = δ-unique (tstep-i₁ ○ merge₂ʳ ○ ⟺ (merge₂ʳ ○ refl⟩⊗⟨ +₁∘i₁))
                         (tstep-i₂ ○ merge₂ʳ ○ ⟺ (merge₂ʳ ○ refl⟩⊗⟨ +₁∘i₂))

tstep-sim : {X′ : Obj} {v : X ⇒ X′} {k : X ⊗₀ A ⇒ X ⊗₀ B} {k′ : X′ ⊗₀ A ⇒ X′ ⊗₀ B}
            {l : X ⊗₀ C ⇒ X ⊗₀ D} {l′ : X′ ⊗₀ C ⇒ X′ ⊗₀ D}
          → v ⊗₁ id ∘ k ≈ k′ ∘ v ⊗₁ id → v ⊗₁ id ∘ l ≈ l′ ∘ v ⊗₁ id
          → v ⊗₁ id ∘ tstep k l ≈ tstep k′ l′ ∘ v ⊗₁ id
tstep-sim {v = v} e₁ e₂ = δ-unique
  (pullʳ tstep-i₁ ○ pullˡ (⟺ (pad-transport v i₁)) ○ assoc ○ (refl⟩∘⟨ e₁)
   ○ ⟺ (pullʳ (⟺ (pad-transport v i₁)) ○ pullˡ tstep-i₁ ○ assoc))
  (pullʳ tstep-i₂ ○ pullˡ (⟺ (pad-transport v i₂)) ○ assoc ○ (refl⟩∘⟨ e₂)
   ○ ⟺ (pullʳ (⟺ (pad-transport v i₂)) ○ pullˡ tstep-i₂ ○ assoc))

onL-tstep : {k : P ⊗₀ A ⇒ P ⊗₀ B} {l : P ⊗₀ C ⇒ P ⊗₀ D}
          → onL {Q = Q} (tstep k l) ≈ tstep (onL k) (onL l)
onL-tstep = δ-unique (onL-branch tstep-i₁ ○ ⟺ tstep-i₁)
                     (onL-branch tstep-i₂ ○ ⟺ tstep-i₂)

onR-tstep : {k : Q ⊗₀ A ⇒ Q ⊗₀ B} {l : Q ⊗₀ C ⇒ Q ⊗₀ D}
          → onR {P = P} (tstep k l) ≈ tstep (onR k) (onR l)
onR-tstep = δ-unique (onR-branch tstep-i₁ ○ ⟺ tstep-i₁)
                     (onR-branch tstep-i₂ ○ ⟺ tstep-i₂)

infixr 10 _⊗ᵉ_

_⊗ᵉ_ : Machine A B → Machine C D → Machine (A + C) (B + D)
f ⊗ᵉ g = mk (state f ⊛ state g) (tstep (onL (step f)) (onR (step g)))

⊗ᵉ-resp-≲ : {f h : Machine A B} {g i : Machine C D}
          → f ≲ h → g ≲ i → (f ⊗ᵉ g) ≲ (h ⊗ᵉ i)
⊗ᵉ-resp-≲ {f = f} {h} {g} {i} u v = record
  { θ       = θ u ⊗₁ θ v
  ; θ-pure  = pure-⊗₁ (θ-pure u) (θ-pure v)
  ; θ-point = ⊛-point₂ (state f) (state h) (state g) (state i) (θ-point u) (θ-point v)
  ; θ-step  = tstep-sim (onL-sim (θ-step u)) (onR-sim (θ-step v))
  }

⊗ᵉ-resp-≈ᴹ : {f h : Machine A B} {g i : Machine C D}
           → f ≈ᴹ h → g ≈ᴹ i → (f ⊗ᵉ g) ≈ᴹ (h ⊗ᵉ i)
⊗ᵉ-resp-≈ᴹ {g = g} e₁ e₂ =
    EqC.gmap (_⊗ᵉ g) (λ s → ⊗ᵉ-resp-≲ s ≲-refl) e₁
  ○ᴹ EqC.gmap (_ ⊗ᵉ_) (⊗ᵉ-resp-≲ ≲-refl) e₂

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

  pureᴹ-∘ : (g : B ⇒ C) (f : A ⇒ B) → (pureᴹ g ∘ᴹ pureᴹ f) ≲ pureᴹ (g ∘ f)
  pureᴹ-∘ g f = collapseˡ ((refl⟩∘⟨ ((onL-str g ⟩∘⟨ onR-id⊗ f) ○ merge₂ˡ))
                           ○ ⟺ (pad-transport λ⇒ (g ∘ f)))

  pure-∘ˡ : (h : B ⇒ C) (M : Machine A B)
          → (pureᴹ h ∘ᴹ M) ≲ mk (state M) (id ⊗₁ h ∘ step M)
  pure-∘ˡ h M = collapseˡ ((refl⟩∘⟨ onL-str h ⟩∘⟨refl) ○ pullˡ (⟺ (pad-transport λ⇒ h))
                           ○ assoc ○ (refl⟩∘⟨ onR-collapseˡ) ○ sym-assoc)

  pure-∘ʳ : (h : A ⇒ B) (M : Machine B C)
          → (M ∘ᴹ pureᴹ h) ≲ mk (state M) (step M ∘ id ⊗₁ h)
  pure-∘ʳ h M = collapseʳ ((refl⟩∘⟨ refl⟩∘⟨ onR-id⊗ h) ○ pullˡ onL-collapseʳ ○ assoc
                           ○ (refl⟩∘⟨ ⟺ (pad-transport ρ⇒ h)) ○ sym-assoc)

⊗ᵉ-pureᴹ : (h : A ⇒ B) (k : C ⇒ D) → (pureᴹ h ⊗ᵉ pureᴹ k) ≲ pureᴹ (h +₁ k)
⊗ᵉ-pureᴹ h k = collapseˡ ((refl⟩∘⟨ (tstep-cong (onL-str h) (onR-id⊗ k)
                                    ○ tstep-str h k))
                          ○ ⟺ (pad-transport λ⇒ (h +₁ k)))

⊗ᵉ-identity : (idᴹ {A} ⊗ᵉ idᴹ {B}) ≲ idᴹ
⊗ᵉ-identity = collapseˡ ((refl⟩∘⟨ (tstep-cong onL-id onR-id ○ tstep-id))
                         ○ identityʳ ○ ⟺ identityˡ)

------------------------------------------------------------------------
-- The structural machines

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
