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

open GradedKleisliTriple ℳ

T₁-⊗ : ∀ u {A B} (h : A ⇒ B) → T₁ u h ≈ id ⊗₁ h
T₁-⊗ u h = begin
    (ρ⇒ ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ (λ⇐ ∘ h)))         ≈⟨ (⟺ triangle) ⟩∘⟨refl ⟩
    ((id ⊗₁ λ⇒) ∘ α⇒) ∘ (α⇐ ∘ (id ⊗₁ (λ⇐ ∘ h)))  ≈⟨ cancelInner associator.isoʳ ⟩
    (id ⊗₁ λ⇒) ∘ (id ⊗₁ (λ⇐ ∘ h))                ≈⟨ merge₂ʳ ⟩
    id ⊗₁ (λ⇒ ∘ (λ⇐ ∘ h))                        ≈⟨ refl⟩⊗⟨ cancelˡ unitorˡ.isoʳ ⟩
    id ⊗₁ h                                      ∎
