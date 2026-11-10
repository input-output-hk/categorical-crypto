{-# OPTIONS --safe --without-K #-}

-- A chosen monoidal discard family is extra data on an arbitrary SMC.

open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Subcategory
import Categories.Category.Monoidal.Braided.Properties as BP
import Categories.Category.Monoidal.Utilities as MU

open import Level

module Categories.Category.Monoidal.Discard
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e) where

open SymmetricMonoidalCategory 𝒱
open BP.Shorthands braided
open MU.Shorthands monoidal
open import Categories.Category.Monoidal.Properties monoidal
open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Morphism.Reasoning U

private variable A B C D : Obj

record MonoidalDiscard : Set (o ⊔ ℓ ⊔ e) where
  field
    discard        : (A : Obj) → A ⇒ unit
    discard-unit   : discard unit ≈ id
    discard-tensor : discard (A ⊗₀ B) ≈ λ⇒ ∘ discard A ⊗₁ discard B

module _ (𝒟 : MonoidalDiscard) where
  open MonoidalDiscard 𝒟

  record PreservesDiscard (f : A ⇒ B) : Set (ℓ ⊔ e) where
    constructor preserving
    field discard-law : discard B ∘ f ≈ discard A

  open PreservesDiscard public

  discard-resp : {f g : A ⇒ B} → f ≈ g → PreservesDiscard f → PreservesDiscard g
  discard-resp eq p = preserving (refl⟩∘⟨ ⟺ eq ○ discard-law p)

  discard-id : PreservesDiscard (id {A})
  discard-id = preserving identityʳ

  discard-compose : {f : B ⇒ C} {g : A ⇒ B}
                  → PreservesDiscard f → PreservesDiscard g → PreservesDiscard (f ∘ g)
  discard-compose p q = preserving (pullˡ (discard-law p) ○ discard-law q)

  discard-product : {f : A ⇒ B} {g : C ⇒ D}
                  → PreservesDiscard f → PreservesDiscard g → PreservesDiscard (f ⊗₁ g)
  discard-product p q = preserving
    (discard-tensor ⟩∘⟨refl ○ assoc ○ refl⟩∘⟨ ⟺ ⊗-distrib-over-∘
     ○ refl⟩∘⟨ discard-law p ⟩⊗⟨ discard-law q ○ ⟺ discard-tensor)

  discard-inverse : {f : A ⇒ B} {g : B ⇒ A}
                  → f ∘ g ≈ id → PreservesDiscard f → PreservesDiscard g
  discard-inverse inv p = preserving (⟺ (discard-law p) ⟩∘⟨refl ○ cancelʳ inv)

  discard-λ⇒ : PreservesDiscard (λ⇒ {A})
  discard-λ⇒ = preserving (⟺ unitorˡ-commute-from ○ refl⟩∘⟨ ⟺ discard-unit ⟩⊗⟨refl ○ ⟺ discard-tensor)

  discard-ρ⇒ : PreservesDiscard (ρ⇒ {A})
  discard-ρ⇒ = preserving (⟺ unitorʳ-commute-from ○ ⟺ coherence₃ ⟩∘⟨ refl⟩⊗⟨ ⟺ discard-unit ○ ⟺ discard-tensor)

  discard-α⇒ : PreservesDiscard (α⇒ {A} {B} {C})
  discard-α⇒ {A} {B} {C} = preserving (begin
    discard (A ⊗₀ (B ⊗₀ C)) ∘ α⇒
      ≈⟨ discard-tensor ⟩∘⟨refl ⟩
    (λ⇒ ∘ discard A ⊗₁ discard (B ⊗₀ C)) ∘ α⇒
      ≈⟨ (refl⟩∘⟨ refl⟩⊗⟨ discard-tensor) ⟩∘⟨refl ⟩
    (λ⇒ ∘ discard A ⊗₁ (λ⇒ ∘ discard B ⊗₁ discard C)) ∘ α⇒
      ≈⟨ (refl⟩∘⟨ split₂ˡ) ⟩∘⟨refl ⟩
    (λ⇒ ∘ id ⊗₁ λ⇒ ∘ discard A ⊗₁ discard B ⊗₁ discard C) ∘ α⇒
      ≈⟨ assoc ○ refl⟩∘⟨ assoc ○ refl⟩∘⟨ refl⟩∘⟨ ⟺ assoc-commute-from ⟩
    λ⇒ ∘ id ⊗₁ λ⇒ ∘ α⇒ ∘ (discard A ⊗₁ discard B) ⊗₁ discard C
      ≈⟨ refl⟩∘⟨ pullˡ triangle ⟩
    λ⇒ ∘ ρ⇒ ⊗₁ id ∘ (discard A ⊗₁ discard B) ⊗₁ discard C
      ≈⟨ refl⟩∘⟨ ⟺ coherence₃ ⟩⊗⟨refl ⟩∘⟨refl ⟩
    λ⇒ ∘ λ⇒ ⊗₁ id ∘ (discard A ⊗₁ discard B) ⊗₁ discard C
      ≈⟨ refl⟩∘⟨ merge₁ˡ ⟩
    λ⇒ ∘ (λ⇒ ∘ discard A ⊗₁ discard B) ⊗₁ discard C
      ≈⟨ refl⟩∘⟨ ⟺ discard-tensor ⟩⊗⟨refl ⟩
    λ⇒ ∘ discard (A ⊗₀ B) ⊗₁ discard C
      ≈˘⟨ discard-tensor ⟩
    discard ((A ⊗₀ B) ⊗₀ C) ∎)

  discard-σ⇒ : PreservesDiscard (σ⇒ {A} {B})
  discard-σ⇒ = preserving
    (discard-tensor ⟩∘⟨refl ○ assoc ○ refl⟩∘⟨ ⟺ σ⇒-comm
     ○ pullˡ (BP.braiding-coherence braided ○ ⟺ coherence₃) ○ ⟺ discard-tensor)

  DiscardSub : WideSymmetricMonoidalSubcategory 𝒱
  DiscardSub = record
    { Selected = PreservesDiscard
    ; selected-resp-≈ = discard-resp
    ; selected-id = discard-id
    ; selected-∘ = discard-compose
    ; selected-⊗₁ = discard-product
    ; selected-λ⇒ = discard-λ⇒
    ; selected-λ⇐ = discard-inverse unitorˡ.isoʳ discard-λ⇒
    ; selected-ρ⇒ = discard-ρ⇒
    ; selected-ρ⇐ = discard-inverse unitorʳ.isoʳ discard-ρ⇒
    ; selected-α⇒ = discard-α⇒
    ; selected-α⇐ = discard-inverse associator.isoʳ discard-α⇒
    ; selected-σ⇒ = discard-σ⇒
    }
