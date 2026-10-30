{-# OPTIONS --safe --without-K #-}

-- Category laws are simulations of one step: unitors collapse a trivial
-- state factor, and associativity rebrackets the state tree.

open import Categories.Category.Core
open import Categories.Category.EquivClosureHelper
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Subcategory
open import Categories.Coherence.Monoidal
open import Categories.Coherence.Monoidal.Tactic
import Categories.Coherence.Symmetric as CS
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

open import Data.Fin
open import Data.Product
open import Data.Vec
open import Level

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Frame as Frame
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.Machines.Category
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e) (𝒫 : WideSymmetricMonoidalSubcategory 𝒱) where

open SymmetricMonoidalCategory 𝒱
open Core 𝒱
open Frame 𝒱
open MonoidalUtilities.Shorthands monoidal
open WideSymmetricMonoidalSubcategory 𝒫
open Sim 𝒱 𝒫

open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Morphism.Reasoning U

private variable A B C D P Q R X Y : Obj
                 f i : Machine A B
                 g : Machine B C
                 h : Machine C D

onR-α : (k : R ⊗₀ X ⇒ R ⊗₀ Y) → α⇒ {P} {Q} ⊗₁ id ∘ onR k ≈ onR (onR k) ∘ α⇒ ⊗₁ id
onR-α k = solve-mor monoidalCategory

onLR-α : (g : Q ⊗₀ X ⇒ Q ⊗₀ Y) → α⇒ ⊗₁ id ∘ onL (onR g) ≈ onR {P = P} (onL {Q = R} g) ∘ α⇒ ⊗₁ id
onLR-α g = solve-mor monoidalCategory

onL-α : (h : P ⊗₀ X ⇒ P ⊗₀ Y) → α⇒ ⊗₁ id ∘ onL (onL h) ≈ onL {Q = Q ⊗₀ R} h ∘ α⇒ ⊗₁ id
onL-α {P = P} {X = X} {Y = Y} {Q = Q} {R = R} h =
  solveH! (S.α⇒ S.⊗₁ S.id S.∘ onLᵗ {q = Var (# 2)} (onLᵗ {q = Var (# 1)} hᵗ)) (onLᵗ hᵗ S.∘ S.α⇒ S.⊗₁ S.id)
  where
    open CS.FreeMonoidalHelper CS.Symm (Fin 5) using (Var) renaming (_⊗₀_ to _⊗ᵒ_)
    open CS.Solver 𝒱 (P ∷ Q ∷ R ∷ X ∷ Y ∷ [])
      (((Var (# 0) ⊗ᵒ Var (# 3)) , (Var (# 0) ⊗ᵒ Var (# 4)) , h) ∷ [])
    βᵗ : ∀ {a b c} → S.HomTerm ((a S.⊗₀ b) S.⊗₀ c) ((a S.⊗₀ c) S.⊗₀ b)
    βᵗ = S.α⇐ S.∘ S.id S.⊗₁ S.σ S.∘ S.α⇒
    onLᵗ : ∀ {p q x y} → S.HomTerm (p S.⊗₀ x) (p S.⊗₀ y)
          → S.HomTerm ((p S.⊗₀ q) S.⊗₀ x) ((p S.⊗₀ q) S.⊗₀ y)
    onLᵗ k = βᵗ S.∘ k S.⊗₁ S.id S.∘ βᵗ
    hᵗ = S.Agen (gen (# 0))

opaque
  unfolding _∘ᴹ_

  assoc-∘ᴹ : (h ∘ᴹ g) ∘ᴹ f ≲ h ∘ᴹ (g ∘ᴹ f)
  assoc-∘ᴹ {h = h} {g = g} {f = f} = sim α⇒ selected-α⇒
    (⊛-assoc-point (state h) (state g) (state f))
    ( refl⟩∘⟨ onL-∘ ⟩∘⟨refl
    ○ refl⟩∘⟨ assoc
    ○ pullˡ (onL-α (step h))
    ○ assoc
    ○ refl⟩∘⟨ pullˡ (onLR-α (step g))
    ○ refl⟩∘⟨ assoc
    ○ refl⟩∘⟨ refl⟩∘⟨ onR-α (step f)
    ○ refl⟩∘⟨ sym-assoc
    ○ refl⟩∘⟨ ⟺ onR-∘ ⟩∘⟨refl
    ○ sym-assoc )

  identityˡ-∘ᴹ : idᴹ ∘ᴹ f ≲ f
  identityˡ-∘ᴹ = collapseˡ (refl⟩∘⟨ (onL-id ⟩∘⟨refl ○ identityˡ) ○ onR-collapseˡ)

  identityʳ-∘ᴹ : f ∘ᴹ idᴹ ≲ f
  identityʳ-∘ᴹ = collapseʳ (refl⟩∘⟨ (refl⟩∘⟨ onR-id ○ identityʳ) ○ onL-collapseʳ)

  ∘ᴹ-resp-≲ : f ≲ h → g ≲ i → f ∘ᴹ g ≲ h ∘ᴹ i
  ∘ᴹ-resp-≲ {f = f} {h = h} {g = g} {i = i} u v = record
    { θ       = θ u ⊗₁ θ v
    ; θ-selected = selected-⊗₁ (θ-selected u) (θ-selected v)
    ; θ-point = ⊛-point₂ (state f) (state h) (state g) (state i) (θ-point u) (θ-point v)
    ; θ-step  = glue′ (onL-sim (θ-step u)) (onR-sim (θ-step v))
    }

Mealy-Category : Category o (o ⊔ ℓ) (o ⊔ ℓ ⊔ e)
Mealy-Category = categoryHelperᵉ record
  { Obj       = Obj
  ; _⇒_       = Machine
  ; _≈_       = _≲_
  ; id        = idᴹ
  ; _∘_       = _∘ᴹ_
  ; assoc     = assoc-∘ᴹ
  ; identityˡ = identityˡ-∘ᴹ
  ; identityʳ = identityʳ-∘ᴹ
  ; ∘-resp-≈  = ∘ᴹ-resp-≲
  }

∘ᴹ-resp-≈ᴹ : f ≈ᴹ h → g ≈ᴹ i → (f ∘ᴹ g) ≈ᴹ (h ∘ᴹ i)
∘ᴹ-resp-≈ᴹ = Category.∘-resp-≈ Mealy-Category
