{-# OPTIONS --safe --without-K #-}

-- Various properties/definitions about SMCs
-- `β` swaps the last two factors of `(P ⊗ Q) ⊗ R`.

open import Categories.Category
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Core
open import Categories.Category.Monoidal.Symmetric
import Categories.Category.Monoidal.Braided.Properties as BraidedProps
import Categories.Category.Monoidal.Utilities as MonoidalUtilities
open import Categories.Coherence.Symmetric.Tactic

open import Data.Product.Base

module Categories.Category.Monoidal.Symmetric.Properties.Ext
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (S : Symmetric M) where

open Category C
open Symmetric S
open BraidedProps.Shorthands braided
open MonoidalUtilities.Shorthands M

open import Categories.Category.Monoidal.Properties M
open import Categories.Category.Monoidal.Reassociation M
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Morphism.Reasoning C
open BraidedProps braided
open MonoidalUtilities M

private variable A B P Q R X Y Z : Obj

private
  𝒱 : SymmetricMonoidalCategory o ℓ e
  𝒱 = record { U = C ; monoidal = M ; symmetric = S }

β : (P ⊗₀ Q) ⊗₀ R ⇒ (P ⊗₀ R) ⊗₀ Q
β = α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒

α⇒-β : α⇒ ∘ β {P} {Q} {R} ≈ id ⊗₁ σ⇒ ∘ α⇒
α⇒-β = cancelˡ associator.isoʳ

β-α⇐ : β {P} {Q} {R} ∘ α⇐ ≈ α⇐ ∘ id ⊗₁ σ⇒
β-α⇐ = assoc ○ refl⟩∘⟨ (assoc ○ refl⟩∘⟨ associator.isoʳ ○ identityʳ)

β-β : β ∘ β ≈ id {(P ⊗₀ Q) ⊗₀ R}
β-β = center (cancelʳ associator.isoʳ) ○ refl⟩∘⟨ cancelˡ (⊗-cancel identity² commutative) ○ associator.isoˡ

σ⊗-inv : σ⇒ ⊗₁ id {P} ∘ σ⇒ {Q} {R} ⊗₁ id ≈ id
σ⊗-inv = merge₁ˡ ○ (commutative ⟩⊗⟨refl) ○ ⊗.identity

pad-braid : (L : Obj) (h : X ⇒ Y) → id {L} ⊗₁ h ≈ σ⇒ ∘ h ⊗₁ id ∘ σ⇒
pad-braid L h = insertˡ commutative ○ (refl⟩∘⟨ braiding.⇒.commute (id , h))

unbraid : (h : X ⇒ Y) {i : A ⇒ P ⊗₀ X} {o : P ⊗₀ Y ⇒ B}
        → o ∘ id ⊗₁ h ∘ i ≈ (o ∘ σ⇒) ∘ h ⊗₁ id ∘ (σ⇒ ∘ i)
unbraid {P = P} h = refl⟩∘⟨ pad-braid P h ⟩∘⟨refl ○ refl⟩∘⟨ assoc ○ sym-assoc ○ refl⟩∘⟨ assoc

σ-splitˡ : σ⇒ {P} {Q ⊗₀ R} ≈ (α⇐ ∘ (id ⊗₁ σ⇒ ∘ (α⇒ ∘ σ⇒ ⊗₁ id))) ∘ α⇐
σ-splitˡ = insertʳ associator.isoʳ ○ ⟺ (cancelˡ associator.isoˡ) ⟩∘⟨refl ○ (refl⟩∘⟨ ⟺ hexagon₁) ⟩∘⟨refl

σ-splitʳ : σ⇒ {P ⊗₀ Q} {R} ≈ α⇒ ∘ ((σ⇒ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ σ⇒) ∘ α⇒
σ-splitʳ = insertˡ associator.isoʳ ○ refl⟩∘⟨ insertʳ associator.isoˡ ○ refl⟩∘⟨ ⟺ hexagon₂ ⟩∘⟨refl

β-nat : (u : P ⇒ Q) (v : R ⇒ Z) (t : X ⇒ Y) → (u ⊗₁ t) ⊗₁ v ∘ β ≈ β ∘ (u ⊗₁ v) ⊗₁ t
β-nat u v t = solve-smc 𝒱

β-natural : (g : X ⇒ Y) → β {P} {Q} ∘ id ⊗₁ g ≈ (id ⊗₁ g) ⊗₁ id ∘ β
β-natural g = refl⟩∘⟨ ⟺ ⊗.identity ⟩⊗⟨refl ○ ⟺ (β-nat id id g)

β-natural′ : (g : X ⇒ Y) → β {P} {Y} {Q} ∘ (id ⊗₁ g) ⊗₁ id ≈ id ⊗₁ g ∘ β
β-natural′ g = ⟺ (β-nat id g id) ○ ⊗.identity ⟩⊗⟨refl ⟩∘⟨refl

σ-unit : σ⇒ {unit} {unit} ≈ id
σ-unit = insertˡ unitorˡ.isoˡ ○ refl⟩∘⟨ (braiding-coherence ○ ⟺ coherence₃) ○ unitorˡ.isoˡ

ρ-β : ρ⇒ {P} ⊗₁ id {Q} ∘ β ≈ ρ⇒
ρ-β = pullˡ (⟺ λ⇒-α⇐) ○ pullˡ (merge₂ʳ ○ refl⟩⊗⟨ braiding-coherence) ○ coherence₂

------------------------------------------------------------------------
-- Tensor-frame actions
------------------------------------------------------------------------

onL : (P ⊗₀ X ⇒ P ⊗₀ Y) → (P ⊗₀ Q) ⊗₀ X ⇒ (P ⊗₀ Q) ⊗₀ Y
onL k = β ∘ k ⊗₁ id ∘ β

onR : (Q ⊗₀ X ⇒ R ⊗₀ Y) → (P ⊗₀ Q) ⊗₀ X ⇒ (P ⊗₀ R) ⊗₀ Y
onR k = α⇐ ∘ id ⊗₁ k ∘ α⇒

onL-∘ : {h₂ : P ⊗₀ Y ⇒ P ⊗₀ B} {h₁ : P ⊗₀ X ⇒ P ⊗₀ Y}
      → onL {Q = Q} (h₂ ∘ h₁) ≈ onL h₂ ∘ onL h₁
onL-∘ = solve-smc 𝒱

onR-∘ : {T V : Obj} {h₂ : R ⊗₀ Y ⇒ T ⊗₀ V} {h₁ : Q ⊗₀ X ⇒ R ⊗₀ Y}
      → onR {P = P} (h₂ ∘ h₁) ≈ onR h₂ ∘ onR h₁
onR-∘ = solve-smc 𝒱

onL-cong : {h h′ : P ⊗₀ X ⇒ P ⊗₀ Y} → h ≈ h′ → onL {Q = Q} h ≈ onL h′
onL-cong e = refl⟩∘⟨ e ⟩⊗⟨refl ⟩∘⟨refl

onR-cong : {h h′ : Q ⊗₀ X ⇒ R ⊗₀ Y} → h ≈ h′ → onR {P = P} h ≈ onR h′
onR-cong e = refl⟩∘⟨ refl⟩⊗⟨ e ⟩∘⟨refl

onL-id : onL {Q = Q} (id {P ⊗₀ A}) ≈ id
onL-id = (refl⟩∘⟨ elimˡ ⊗.identity) ○ β-β

onR-id : onR {P = P} (id {Q ⊗₀ A}) ≈ id
onR-id = (refl⟩∘⟨ elimˡ ⊗.identity) ○ associator.isoˡ

onL-id⊗ : (g : X ⇒ Y) → onL {Q = Q} (id {P} ⊗₁ g) ≈ id ⊗₁ g
onL-id⊗ g = (refl⟩∘⟨ ⟺ (β-natural g)) ○ cancelˡ β-β

onR-id⊗ : (h : X ⇒ Y) → onR {Q = Q} {P = P} (id ⊗₁ h) ≈ id ⊗₁ h
onR-id⊗ h = pullˡ (⟺ α⇐-id⊗-commute) ○ cancelʳ associator.isoˡ

onL-branch : {k : P ⊗₀ A ⇒ P ⊗₀ B} {t : P ⊗₀ X ⇒ P ⊗₀ Y} {j : A ⇒ X} {j′ : B ⇒ Y}
           → t ∘ id ⊗₁ j ≈ id ⊗₁ j′ ∘ k → onL {Q = Q} t ∘ id ⊗₁ j ≈ id ⊗₁ j′ ∘ onL k
onL-branch {j = j} {j′} e =
  refl⟩∘⟨ ⟺ (onL-id⊗ j) ○ ⟺ onL-∘ ○ onL-cong e ○ onL-∘ ○ onL-id⊗ j′ ⟩∘⟨refl

onR-branch : {k : P ⊗₀ A ⇒ P ⊗₀ B} {t : P ⊗₀ X ⇒ P ⊗₀ Y} {j : A ⇒ X} {j′ : B ⇒ Y}
           → t ∘ id ⊗₁ j ≈ id ⊗₁ j′ ∘ k → onR {P = Q} t ∘ id ⊗₁ j ≈ id ⊗₁ j′ ∘ onR k
onR-branch {j = j} {j′} e =
  refl⟩∘⟨ ⟺ (onR-id⊗ j) ○ ⟺ onR-∘ ○ onR-cong e ○ onR-∘ ○ onR-id⊗ j′ ⟩∘⟨refl

onL-sim : {v : P ⇒ R} {w : Q ⇒ Z} {k : P ⊗₀ X ⇒ P ⊗₀ Y} {k′ : R ⊗₀ X ⇒ R ⊗₀ Y}
        → v ⊗₁ id ∘ k ≈ k′ ∘ v ⊗₁ id → (v ⊗₁ w) ⊗₁ id ∘ onL k ≈ onL k′ ∘ (v ⊗₁ w) ⊗₁ id
onL-sim {v = v} {w} e =
  extendʳ (β-nat v id w) ○ refl⟩∘⟨ extendʳ (parallel e id-comm) ○ refl⟩∘⟨ refl⟩∘⟨ β-nat v w id ○ assoc²εβ

onR-sim : {v : P ⇒ R} {w : Q ⇒ Z} {k : Q ⊗₀ X ⇒ Q ⊗₀ Y} {k′ : Z ⊗₀ X ⇒ Z ⊗₀ Y}
        → w ⊗₁ id ∘ k ≈ k′ ∘ w ⊗₁ id → (v ⊗₁ w) ⊗₁ id ∘ onR k ≈ onR k′ ∘ (v ⊗₁ w) ⊗₁ id
onR-sim e = extendʳ (⟺ assoc-commute-to) ○ refl⟩∘⟨ extendʳ (parallel id-comm e)
  ○ refl⟩∘⟨ refl⟩∘⟨ ⟺ assoc-commute-from ○ assoc²εβ

σ-onR : {k : Q ⊗₀ A ⇒ Q ⊗₀ B} → σ⇒ ⊗₁ id ∘ onR k ≈ onL {Q = P} k ∘ σ⇒ ⊗₁ id
σ-onR = solve-smc 𝒱

σ-onL : {k : P ⊗₀ A ⇒ P ⊗₀ B} → σ⇒ ⊗₁ id ∘ onL k ≈ onR {P = Q} k ∘ σ⇒ ⊗₁ id
σ-onL = solve-smc 𝒱

onR-collapseˡ : {k : Q ⊗₀ A ⇒ Q ⊗₀ B} → λ⇒ ⊗₁ id ∘ onR k ≈ k ∘ λ⇒ ⊗₁ id
onR-collapseˡ = solve-smc 𝒱

onL-collapseʳ : {k : P ⊗₀ A ⇒ P ⊗₀ B} → ρ⇒ ⊗₁ id ∘ onL k ≈ k ∘ ρ⇒ ⊗₁ id
onL-collapseʳ = solve-smc 𝒱

onR-α : (k : R ⊗₀ X ⇒ R ⊗₀ Y) → α⇒ {P} {Q} ⊗₁ id ∘ onR k ≈ onR (onR k) ∘ α⇒ ⊗₁ id
onR-α k = solve-smc 𝒱

onLR-α : (g : Q ⊗₀ X ⇒ Q ⊗₀ Y) → α⇒ ⊗₁ id ∘ onL (onR g) ≈ onR {P = P} (onL {Q = R} g) ∘ α⇒ ⊗₁ id
onLR-α g = solve-smc 𝒱

onL-α : (h : P ⊗₀ X ⇒ P ⊗₀ Y) → α⇒ ⊗₁ id ∘ onL (onL h) ≈ onL {Q = Q ⊗₀ R} h ∘ α⇒ ⊗₁ id
onL-α h = solve-smc 𝒱
