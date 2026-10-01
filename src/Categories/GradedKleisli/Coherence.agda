{-# OPTIONS --safe --without-K #-}

-- The coherence equations behind `Categories.GradedKleisli`'s category laws and
-- `U-∘`, stated over an arbitrary monoidal category.  Kept apart because each
-- `solve-mor` call holds ~0.1 GiB of residency until the end of its module;
-- discharged inside `GradedKleisli` they took it past a 3 GiB heap.

open import Level

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Coherence.Monoidal.Tactic

module Categories.GradedKleisli.Coherence {o ℓ e : Level} (I : MonoidalCategory o ℓ e) where

open MonoidalCategory I
open import Categories.Category.Monoidal.Utilities monoidal
open Shorthands

private variable A B C D a b c d : Obj

slide-assoc : (f : A ⊗₀ a ⇒ B) (g : B ⊗₀ b ⇒ C) (h : C ⊗₀ c ⇒ D)
            → (h ∘ ((g ∘ (f ⊗₁ id) ∘ α⇐) ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ α⇐)
            ≈ (h ∘ (g ⊗₁ id) ∘ α⇐) ∘ (f ⊗₁ id) ∘ α⇐
slide-assoc _ _ _ = solve-mor I

slide-identityˡ : (f : A ⊗₀ a ⇒ B) → f ∘ (id ⊗₁ ρ⇒) ≈ ρ⇒ ∘ (f ⊗₁ id) ∘ α⇐
slide-identityˡ _ = solve-mor I

slide-identityʳ : (f : A ⊗₀ a ⇒ B) → f ∘ (id ⊗₁ λ⇒) ≈ f ∘ (ρ⇒ ⊗₁ id) ∘ α⇐
slide-identityʳ _ = solve-mor I

slide-∘-resp : (h : B ⊗₀ b ⇒ C) (i : A ⊗₀ a ⇒ B) (ψ : c ⇒ a) (φ : d ⇒ b)
             → (h ∘ (i ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ (ψ ⊗₁ φ))
             ≈ (h ∘ id ⊗₁ φ) ∘ (i ∘ id ⊗₁ ψ) ⊗₁ id ∘ α⇐
slide-∘-resp _ _ _ _ = solve-mor I

sub-assoc : (f : B ⊗₀ b ⇒ C) (g : A ⊗₀ a ⇒ B) → (f ∘ (g ⊗₁ id) ∘ α⇐) ∘ α⇒ ≈ f ∘ (g ⊗₁ id)
sub-assoc _ _ = solve-mor I
