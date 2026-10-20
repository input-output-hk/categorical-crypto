{-# OPTIONS --safe --without-K #-}

-- Parallel composition needs a monoidal structure on the 𝒞 and an
-- effect-combination map. UC-⊠ requires contextual congruence.

module CategoricalCrypto.Abstract2.Parallel where

open import Data.Product
open import Level

open import Categories.Category.Monoidal

open import CategoricalCrypto.Abstract2
open import CategoricalCrypto.UCSetup

module ParallelUC
  {o ℓ e o′ ℓ′ e′ cs ℓs : Level}
  (setup : UCSetup o ℓ e o′ ℓ′ e′ cs ℓs)
  (Monoidal-𝒞 : Monoidal (UCSetup.𝒞 setup))
  where
  open AbstractUC setup hiding (module 𝒞)
  module 𝒞 where
    open Monoidal Monoidal-𝒞 public
    open AbstractUC.𝒞 setup public

  private variable
    A B C D : 𝒞.Obj
    X X′ Y Y′ : ℐ.Obj

  TensorStable : Set (o′ ⊔ ℓ′ ⊔ cs ⊔ ℓs)
  TensorStable = ∀ {A B C D} {f f′ : A 𝒞.⇒ B} {h h′ : C 𝒞.⇒ D}
               → f ≈ℰ f′ → h ≈ℰ h′ → f 𝒞.⊗₁ h ≈ℰ f′ 𝒞.⊗₁ h′

  record ParallelEffect : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ e′) where
    field
      χ : T₀ X B 𝒞.⊗₀ T₀ Y D 𝒞.⇒ T₀ (X ⊗₀ Y) (B 𝒞.⊗₀ D)
      χ-sub : (a : X ℐ.⇒ X′) (b : Y ℐ.⇒ Y′)
            → χ 𝒞.∘ sub a 𝒞.⊗₁ sub b 𝒞.≈ sub (a ⊗₁ b) 𝒞.∘ χ {B = B} {D = D}

    infixr 10 _⊠_
    _⊠_ : A 𝒞.⇒ T₀ X B → C 𝒞.⇒ T₀ Y D → A 𝒞.⊗₀ C 𝒞.⇒ T₀ (X ⊗₀ Y) (B 𝒞.⊗₀ D)
    f ⊠ g = χ 𝒞.∘ f 𝒞.⊗₁ g

    ParallelStable : Set (o ⊔ o′ ⊔ ℓ′ ⊔ cs ⊔ ℓs)
    ParallelStable = ∀ {A B C D X Y} {f f′ : A 𝒞.⇒ T₀ X B} {g g′ : C 𝒞.⇒ T₀ Y D}
      → f ≈ᵁ f′ → g ≈ᵁ g′ → f ⊠ g ≈ᵁ f′ ⊠ g′

    ⊠-sub : (a : X ℐ.⇒ X′) (b : Y ℐ.⇒ Y′) (f : A 𝒞.⇒ T₀ X B) (g : C 𝒞.⇒ T₀ Y D)
      → (sub a 𝒞.∘ f) ⊠ (sub b 𝒞.∘ g) 𝒞.≈ sub (a ⊗₁ b) 𝒞.∘ f ⊠ g
    ⊠-sub a b f g = let open 𝒞 in begin
        χ ∘ ((sub a ∘ f) 𝒞.⊗₁ (sub b ∘ g))     ≈⟨ refl⟩∘⟨ 𝒞.⊗.homomorphism ⟩
        χ ∘ (sub a 𝒞.⊗₁ sub b) ∘ (f 𝒞.⊗₁ g)    ≈⟨ sym-assoc ⟩
        (χ ∘ (sub a 𝒞.⊗₁ sub b)) ∘ (f 𝒞.⊗₁ g)  ≈⟨ χ-sub a b ⟩∘⟨refl ⟩
        (sub (a ℐ.⊗₁ b) ∘ χ) ∘ (f 𝒞.⊗₁ g)      ≈⟨ assoc ⟩
        sub (a ℐ.⊗₁ b) ∘ f ⊠ g                 ∎

    ⊠-cong-≈ᵁ : GradeStable → TensorStable → ParallelStable
    ⊠-cong-≈ᵁ gs ts ef eh = bridge gs (≈ℰ-cong-post χ (ts (≈ᵁ⇒≈ℰ ef) (≈ᵁ⇒≈ℰ eh)))

    UC-⊠ : ParallelStable → ∀ {A B C D X X′ Y Y′}
      {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ X′ B}
      {h : C 𝒞.⇒ T₀ Y D} {k : C 𝒞.⇒ T₀ Y′ D}
      → f ≤UC g → h ≤UC k → f ⊠ h ≤UC g ⊠ k
    UC-⊠ ps f≤g h≤k =
      let sf , ef = ≤UC⇒dummy f≤g
          sh , eh = ≤UC⇒dummy h≤k
      in dummy-complete (sf ⊗₁ sh , ≈ᵁ-trans (ps ef eh) (≈C⇒≈ᵁ (⊠-sub sf sh _ _)))
