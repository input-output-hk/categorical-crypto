{-# OPTIONS --safe --without-K #-}

module Categories.GConstruction.Core where

open import Categories.Category
open import Categories.Category.Monoidal.Core
open import Categories.Category.Monoidal.Symmetric
open import Categories.Category.Monoidal.Traced
import Categories.Category.Monoidal.Braided.Properties as BProps
import Categories.Category.Monoidal.Utilities as U
open import Data.Product

-- Target and free symmetric categories use identical composition trees.
module Wiring {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (S : Symmetric M) where
  open Category C
  open Symmetric S
  open U.Shorthands M
  open BProps.Shorthands braided
  open import Categories.Category.Monoidal.Symmetric.Properties.Ext S public using (β)

  α : ∀ {A⁻ B⁺ B⁻ C⁺} → (B⁻ ⊗₀ C⁺) ⊗₀ (A⁻ ⊗₀ B⁺) ⇒ (A⁻ ⊗₀ C⁺) ⊗₀ (B⁻ ⊗₀ B⁺)
  α = α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (σ⇒ ⊗₁ id) ∘ id ⊗₁ α⇐ ∘ α⇒

  γ : ∀ {A⁺ B⁺ B⁻ C⁻} → (A⁺ ⊗₀ C⁻) ⊗₀ (B⁻ ⊗₀ B⁺) ⇒ (B⁺ ⊗₀ C⁻) ⊗₀ (A⁺ ⊗₀ B⁻)
  γ = α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (σ⇒ ⊗₁ id) ∘ id ⊗₁ α⇐ ∘ α⇒ ∘ id ⊗₁ σ⇒

  mid : ∀ {P Q R S} → (P ⊗₀ Q) ⊗₀ (R ⊗₀ S) ⇒ (P ⊗₀ R) ⊗₀ (Q ⊗₀ S)
  mid = α⇐ ∘ id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒

module Construction {a b c} (C : Category a b c) (M : Monoidal C) (T : Traced M) where
  open Category C
  open Traced T
  open U.Shorthands M
  open BProps.Shorthands braided
  open Wiring symmetric

  _⇒ᴳ_ : Obj × Obj → Obj × Obj → Set b
  (A⁺ , A⁻) ⇒ᴳ (B⁺ , B⁻) = A⁺ ⊗₀ B⁻ ⇒ A⁻ ⊗₀ B⁺

  opaque
    composeᴳ : ∀ {A B D} → B ⇒ᴳ D → A ⇒ᴳ B → A ⇒ᴳ D
    composeᴳ f g = trace (α ∘ f ⊗₁ g ∘ γ)

  _⊗₀ᴳ_ : Obj × Obj → Obj × Obj → Obj × Obj
  (A⁺ , A⁻) ⊗₀ᴳ (B⁺ , B⁻) = A⁺ ⊗₀ B⁺ , A⁻ ⊗₀ B⁻

  unitᴳ : Obj × Obj
  unitᴳ = unit , unit

  opaque
    infixr 10 _⊗₁ᴳ_
    _⊗₁ᴳ_ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ E⁺ E⁻ : Obj} →
            A⁺ ⊗₀ B⁻ ⇒ A⁻ ⊗₀ B⁺ → D⁺ ⊗₀ E⁻ ⇒ D⁻ ⊗₀ E⁺ →
            (A⁺ ⊗₀ D⁺) ⊗₀ (B⁻ ⊗₀ E⁻) ⇒ (A⁻ ⊗₀ D⁻) ⊗₀ (B⁺ ⊗₀ E⁺)
    f ⊗₁ᴳ g = mid ∘ f ⊗₁ g ∘ mid

  ⌜_,_⌝ : ∀ {A⁺ A⁻ B⁺ B⁻ : Obj} → A⁺ ⇒ B⁺ → B⁻ ⇒ A⁻ → A⁺ ⊗₀ B⁻ ⇒ A⁻ ⊗₀ B⁺
  ⌜ u , v ⌝ = σ⇒ ∘ u ⊗₁ v
