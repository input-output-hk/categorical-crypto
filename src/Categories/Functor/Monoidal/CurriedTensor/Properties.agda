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

-- The triple's data, read back in the monoidal vocabulary.  `T₁` is the only
-- one that is not the definition: the record derives it as
-- `sub ρ⇒ ∘ ext u (return ∘ -)`, so its being the tensor's own `F₁` costs one
-- triangle and one unitor cancellation.
sub-⊗ : {u v : Obj} (α : u ⇒ v) {A : Obj} → sub α {A} ≈ α ⊗₁ id
sub-⊗ _ = Equiv.refl

return-λ⇐ : {A : Obj} → return {A} ≈ λ⇐
return-λ⇐ = Equiv.refl

ext-⊗ : ∀ u {v A B} (f : A ⇒ T₀ v B) → ext u f ≈ α⇐ ∘ id ⊗₁ f
ext-⊗ _ _ = Equiv.refl

μ-α⇐ : ∀ u v {A} → μ u v {A} ≈ α⇐
μ-α⇐ _ _ = elimʳ ⊗.identity

T₁-⊗ : ∀ u {A B} (h : A ⇒ B) → T₁ u h ≈ id ⊗₁ h
T₁-⊗ u h = begin
    (ρ⇒ ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ (λ⇐ ∘ h)))         ≈⟨ (⟺ triangle) ⟩∘⟨refl ⟩
    ((id ⊗₁ λ⇒) ∘ α⇒) ∘ (α⇐ ∘ (id ⊗₁ (λ⇐ ∘ h)))  ≈⟨ cancelInner associator.isoʳ ⟩
    (id ⊗₁ λ⇒) ∘ (id ⊗₁ (λ⇐ ∘ h))                ≈⟨ merge₂ʳ ⟩
    id ⊗₁ (λ⇒ ∘ (λ⇐ ∘ h))                        ≈⟨ refl⟩⊗⟨ cancelˡ unitorˡ.isoʳ ⟩
    id ⊗₁ h                                      ∎

-- The prefix `_≈ᵁ_` compares (`Abstract2`): it is a BRACKETING of the test's
-- domain and nothing else, which is what gives the U-kernel its operational
-- reading (`CategoricalCrypto.UC.Model.Reading`).
μT₁-α⇐ : ∀ u {v A B} (f : A ⇒ T₀ v B) → μ u v ∘ T₁ u f ≈ α⇐ ∘ id ⊗₁ f
μT₁-α⇐ u f = ∘-resp-≈ (μ-α⇐ u _) (T₁-⊗ u f)
