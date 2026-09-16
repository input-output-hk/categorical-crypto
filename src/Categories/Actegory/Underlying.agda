{-# OPTIONS --safe --without-K #-}

-- The locally graded category Ψ 𝒟 underlying an ℐ-actegory 𝒟

module Categories.Actegory.Underlying where

open import Level

open import Categories.Actegory
open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Functor
open import Categories.LocallyGraded
import Categories.Morphism.Reasoning as MR

module _ {o ℓ e o′ ℓ′ e′} {ℐ : MonoidalCategory o ℓ e} {𝒟 : Category o′ ℓ′ e′} where
  private
    module ℐ = MonoidalCategory ℐ
    module 𝒟 = Category 𝒟

  Ψ : Actegory ℐ 𝒟 → LocallyGradedCategory ℐ o′ ℓ′ e′
  Ψ act = record
    { Obj = 𝒟.Obj
    ; Hom = λ X A B → A ⇒ X ∗₀ B
    ; _≈_ = _≈_
    ; equiv = equiv
    ; sub[_] = λ a f → a ∗₁ 𝒟.id ∘ f
    ; sub-identity = elimˡ ∗-identity
    ; sub-homomorphism = pushˡ (∗-resp-≈ ℐ.Equiv.refl (⟺ identity²) ○ ∗-homomorphism)
    ; sub-resp-≈ = λ a≈ f≈ → ∗-resp-≈ a≈ Equiv.refl ⟩∘⟨ f≈
    ; id = unitor.to
    ; _∙_ = λ g f → multiplicator.to ∘ ℐ.id ∗₁ g ∘ f
    ; ∙-resp-≈ = λ g≈ f≈ → refl⟩∘⟨ (∗-resp-≈ ℐ.Equiv.refl g≈ ⟩∘⟨ f≈)
    ; identityˡ = (refl⟩∘⟨ sym-assoc) ○ pullˡ unitʳ-coherence-to ○ identityˡ
    ; identityʳ = (refl⟩∘⟨ (refl⟩∘⟨ ⟺ unitor-commute-to)) ○ (refl⟩∘⟨ sym-assoc)
        ○ pullˡ unitˡ-coherence-to ○ identityˡ
    ; assoc = (refl⟩∘⟨ ((split ○ (refl⟩∘⟨ split)) ⟩∘⟨refl))
        ○ (refl⟩∘⟨ assoc) ○ sym-assoc
        ○ (⟺ assoc-coherence-to ⟩∘⟨ assoc)
        ○ assoc ○ (refl⟩∘⟨ assoc)
        ○ (refl⟩∘⟨ (refl⟩∘⟨ pullˡ multiplicator-commute-to))
        ○ (refl⟩∘⟨ (refl⟩∘⟨ ((∗-resp-≈ (Functor.identity ℐ.⊗) Equiv.refl ⟩∘⟨refl) ⟩∘⟨refl)))
        ○ (refl⟩∘⟨ (refl⟩∘⟨ assoc))
    ; interchange = (refl⟩∘⟨ sym-assoc)
        ○ (refl⟩∘⟨ (decompʳ ⟩∘⟨refl))
        ○ (refl⟩∘⟨ ((∗-resp-≈ (ℐ.Equiv.sym ℐ.identityʳ) Equiv.refl ○ ∗-homomorphism) ⟩∘⟨refl))
        ○ (refl⟩∘⟨ assoc)
        ○ pullˡ multiplicator-commute-to
        ○ assoc
    }
    where
    open Actegory act
    open 𝒟
    open 𝒟.HomReasoning
    open MR 𝒟

    split : ∀ {x A B C} {u : B ⇒ C} {w : A ⇒ B}
          → ℐ.id {x} ∗₁ (u ∘ w) ≈ (ℐ.id ∗₁ u) ∘ (ℐ.id ∗₁ w)
    split = ∗-resp-≈ (ℐ.Equiv.sym ℐ.identity²) Equiv.refl ○ ∗-homomorphism
