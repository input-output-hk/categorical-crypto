{-# OPTIONS --safe --without-K #-}

-- `β` swaps the last two factors of `(P ⊗ Q) ⊗ R`.

open import Categories.Category
open import Categories.Category.Monoidal.Core
open import Categories.Category.Monoidal.Symmetric
import Categories.Category.Monoidal.Braided.Properties as BraidedProps
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

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
unbraid {P = P} h = refl⟩∘⟨ pad-braid P h ⟩∘⟨refl ○ refl⟩∘⟨ assoc ○ sym-assoc
                  ○ refl⟩∘⟨ assoc

σ-splitˡ : σ⇒ {P} {Q ⊗₀ R} ≈ (α⇐ ∘ (id ⊗₁ σ⇒ ∘ (α⇒ ∘ σ⇒ ⊗₁ id))) ∘ α⇐
σ-splitˡ = insertʳ associator.isoʳ ○ ⟺ (cancelˡ associator.isoˡ) ⟩∘⟨refl ○ (refl⟩∘⟨ ⟺ hexagon₁) ⟩∘⟨refl

σ-splitʳ : σ⇒ {P ⊗₀ Q} {R} ≈ α⇒ ∘ ((σ⇒ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ σ⇒) ∘ α⇒
σ-splitʳ = insertˡ associator.isoʳ ○ refl⟩∘⟨ insertʳ associator.isoˡ ○ refl⟩∘⟨ ⟺ hexagon₂ ⟩∘⟨refl

β-nat : (u : P ⇒ Q) (v : R ⇒ Z) (t : X ⇒ Y) → (u ⊗₁ t) ⊗₁ v ∘ β ≈ β ∘ (u ⊗₁ v) ⊗₁ t
β-nat u v t = begin
  (u ⊗₁ t) ⊗₁ v ∘ α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒
    ≈⟨ pullˡ (⟺ assoc-commute-to) ○ assoc ⟩
  α⇐ ∘ u ⊗₁ t ⊗₁ v ∘ id ⊗₁ σ⇒ ∘ α⇒
    ≈⟨ refl⟩∘⟨ pullˡ (parallel id-comm (⟺ (braiding.⇒.commute (v , t)))) ⟩
  α⇐ ∘ (id ⊗₁ σ⇒ ∘ u ⊗₁ v ⊗₁ t) ∘ α⇒
    ≈⟨ refl⟩∘⟨ assoc ⟩
  α⇐ ∘ id ⊗₁ σ⇒ ∘ u ⊗₁ v ⊗₁ t ∘ α⇒
    ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc-commute-from ⟩
  α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒ ∘ (u ⊗₁ v) ⊗₁ t
    ≈⟨ refl⟩∘⟨ sym-assoc ○ sym-assoc ⟩
  (α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒) ∘ (u ⊗₁ v) ⊗₁ t ∎

β-natural : (g : X ⇒ Y) → β {P} {Q} ∘ id ⊗₁ g ≈ (id ⊗₁ g) ⊗₁ id ∘ β
β-natural g = refl⟩∘⟨ ⟺ ⊗.identity ⟩⊗⟨refl ○ ⟺ (β-nat id id g)

β-natural′ : (g : X ⇒ Y) → β {P} {Y} {Q} ∘ (id ⊗₁ g) ⊗₁ id ≈ id ⊗₁ g ∘ β
β-natural′ g = ⟺ (β-nat id g id) ○ ⊗.identity ⟩⊗⟨refl ⟩∘⟨refl

σ-unit : σ⇒ {unit} {unit} ≈ id
σ-unit = insertˡ unitorˡ.isoˡ ○ refl⟩∘⟨ (braiding-coherence ○ ⟺ coherence₃) ○ unitorˡ.isoˡ

ρ-β : ρ⇒ {P} ⊗₁ id {Q} ∘ β ≈ ρ⇒
ρ-β = pullˡ (⟺ λ⇒-α⇐) ○ pullˡ (merge₂ʳ ○ refl⟩⊗⟨ braiding-coherence) ○ coherence₂
