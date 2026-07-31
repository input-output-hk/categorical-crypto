{-# OPTIONS --safe --without-K #-}

open import Categories.Category.Monoidal

module Categories.Functor.Monoidal.CurriedTensor.Properties
  {o ℓ e} (M : MonoidalCategory o ℓ e) where

import Categories.Category.Monoidal.Reasoning as MonoidalR
import Categories.Category.Monoidal.Utilities as MonoidalUtilities
import Categories.Morphism.Reasoning as MR
open import Categories.Functor.Monoidal.CurriedTensor M
open import Categories.Monad.Graded

open MonoidalCategory M
open MonoidalR monoidal
open MonoidalUtilities.Shorthands monoidal
open MR U

private
  ℳ : GradedKleisliTriple M U
  ℳ = GradedMonad⇒GradedKleisliTriple curriedTensor

open GradedKleisliTriple ℳ using (T₁)

T₁-⊗ : ∀ u {A B} (h : A ⇒ B) → T₁ u h ≈ id ⊗₁ h
T₁-⊗ u h = begin
    (ρ⇒ ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ (λ⇐ ∘ h)))                 ≈⟨ refl⟩∘⟨ refl⟩∘⟨ split₂ˡ ⟩
    (ρ⇒ ⊗₁ id) ∘ (α⇐ ∘ ((id ⊗₁ λ⇐) ∘ (id ⊗₁ h)))         ≈⟨ (⟺ triangle) ⟩∘⟨refl ⟩
    ((id ⊗₁ λ⇒) ∘ α⇒) ∘ (α⇐ ∘ ((id ⊗₁ λ⇐) ∘ (id ⊗₁ h)))  ≈⟨ cancelInner associator.isoʳ ⟩
    (id ⊗₁ λ⇒) ∘ ((id ⊗₁ λ⇐) ∘ (id ⊗₁ h))                ≈⟨ pullˡ merge₂ˡ ⟩
    (id ⊗₁ (λ⇒ ∘ λ⇐)) ∘ (id ⊗₁ h)                        ≈⟨ elimˡ ((refl⟩⊗⟨ unitorˡ.isoʳ) ○ ⊗.identity) ⟩
    id ⊗₁ h                                              ∎
